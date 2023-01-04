{-# LANGUAGE DataKinds           #-}  
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-} 
{-# LANGUAGE NoImplicitPrelude   #-}  
{-# LANGUAGE ScopedTypeVariables #-} 
{-# LANGUAGE TemplateHaskell     #-}  
{-# LANGUAGE TypeApplications    #-}  
{-# LANGUAGE TypeFamilies        #-} 
{-# LANGUAGE TypeOperators       #-}  
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE OverloadedStrings   #-}  

module Booking where

--PlutusTx 
import qualified PlutusTx
import qualified PlutusTx.Builtins              as Builtins
import           PlutusTx.Prelude               hiding (Semigroup(..), unless)
--Contract Monad
import           Plutus.Contract               
-- Ledger 
import           Ledger                         hiding (singleton)
import           Ledger.Address              
import           Ledger.Constraints             as Constraints            
-- Plutus
import qualified Plutus.V2.Ledger.Api           as PlutusV2             
import           Plutus.Script.Utils.V2.Typed.Scripts as TypedScriptsV2   
import           Plutus.Script.Utils.V2.Scripts as ScriptsV2             
import           Ledger.Ada                     as Ada 
import           Plutus.V2.Ledger.Contexts      as ContextV2
import           PlutusTx.Builtins.Class        as Class
--Trace Emulator
import           Plutus.Trace
import qualified Plutus.Trace.Emulator          as Emulator
import qualified Wallet.Emulator.Wallet         as Wallet


import           Playground.Contract  (printJson, printSchemas, ensureKnownCurrencies, stage, ToSchema)
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Text.Printf          (printf)

import           Prelude              (IO, Semigroup (..), String)
import           Control.Monad        hiding (fmap)
import           Data.Map             as Map
import           Data.Text            (Text)
import           Data.Void            (Void)
import           Data.Aeson           (FromJSON, ToJSON)
import           GHC.Generics         (Generic)

import           Control.Monad                  hiding (fmap)
import           Data.Map                       as Map
import           Data.Text                      (Text)
import           Data.Void                      (Void)
import           Prelude                        (IO, Semigroup (..), String, show)
import           Text.Printf                    (printf)
import           Control.Monad.Freer.Extras     as Extras


import           Data.String (IsString(fromString))
import           Data.Either (fromRight)
import           Data.Text (Text, pack)
import           Ledger (PubKeyHash(..), pubKeyHash) 
import           Ledger.Bytes (LedgerBytes(LedgerBytes), fromHex)

data BookingInfo = BookingInfo 
    { customer      :: PaymentPubKeyHash
    , aValue        :: Integer
    }
     deriving (Generic, FromJSON, ToJSON, ToSchema)
     

newtype BookingRedeemer  = BookingRedeemer  Integer deriving (Generic, FromJSON, ToJSON, ToSchema)


PlutusTx.unstableMakeIsData ''BookingInfo
PlutusTx.unstableMakeIsData ''BookingRedeemer


{-# INLINABLE  bookingValidator #-}
bookingValidator :: BookingInfo -> BookingRedeemer -> PlutusV2.ScriptContext -> Bool
bookingValidator bd br sc  
    | traceIfFalse ("Wrong pkey using checkSign function") checkSig   = True -- Test checking if the puKey hash is in the signature list (dosn't work)
    | traceIfFalse ("Wrong pkey using signBuy function") signBuy      = True -- Test using txSignBy function (dosn't work)
    | traceIfFalse ("Wrong value") (aValue bd == 4)                   = True -- Test to validate that the problem dosn't come from the datum
    | otherwise = False
    where 
        info :: PlutusV2.TxInfo
        info = PlutusV2.scriptContextTxInfo sc

        customerPKH :: PubKeyHash
        customerPKH = unPaymentPubKeyHash (customer bd) 

        checkSig :: Bool
        checkSig = customerPKH `elem` ContextV2.txInfoSignatories info

        signBuy :: Bool
        signBuy = ContextV2.txSignedBy info customerPKH 
     
data Booking
instance TypedScriptsV2.ValidatorTypes Booking where
    type instance RedeemerType Booking = BookingRedeemer
    type instance DatumType Booking = BookingInfo

typedValidator :: TypedScriptsV2.TypedValidator Booking
typedValidator = TypedScriptsV2.mkTypedValidator @Booking 
        $$(PlutusTx.compile [|| bookingValidator ||])
        $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = TypedScriptsV2.mkUntypedValidator @BookingInfo @BookingRedeemer

validator :: Validator
validator = TypedScriptsV2.validatorScript typedValidator  

-- The hash of the validators
valHash :: Ledger.ValidatorHash
valHash = TypedScriptsV2.validatorHash typedValidator 

-- Script address 
scrAddress :: Address
scrAddress = TypedScriptsV2.validatorAddress typedValidator 

--THE OFFCHAIN RELATED CODE
type GiftSchema =
            Endpoint "give" GiveParam 
        .\/ Endpoint "grab" Integer

data GiveParam = GiveParam 
     { gAmount     :: Integer
     , bookingInfo :: BookingInfo}
    deriving (Generic, FromJSON, ToJSON, ToSchema)

give :: AsContractError e => GiveParam -> Contract w s e ()
give gp = do
    pkh <- Plutus.Contract.ownPaymentPubKeyHash
    let datum = BookingInfo 
                { customer = pkh
                , aValue   = aValue $ bookingInfo $ gp
                }

    let tx = mustPayToTheScriptWithDatumInTx datum $ Ada.lovelaceValueOf $ gAmount gp                
    ledgerTx <- submitTxConstraints typedValidator tx                                                
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx                                                
    Plutus.Contract.logInfo @String $ "Tx ID: " ++ show (getCardanoTxId ledgerTx)  
    Plutus.Contract.logInfo @String $ "Unspent UTXO output: " ++ show (getCardanoTxOutRefs ledgerTx) 
    Plutus.Contract.logInfo @String $ "Payment PubKey Hash2: " ++ show (pkh)


grab :: forall w s e. AsContractError e => Integer -> Contract w s e ()                                     
grab n = do
    utxos <- utxosAt scrAddress                                                                    
    let orefs   = fst <$> Map.toList utxos                         
                                                                                                    
        lookups = Constraints.unspentOutputs utxos      <>                                          
                    Constraints.plutusV2OtherScript validator 
         
        r :: BookingRedeemer
        r = BookingRedeemer n

        tx :: TxConstraints Void Void                                                            
        tx      = mconcat [mustSpendScriptOutput oref $ Redeemer $ PlutusTx.toBuiltinData r | oref <- orefs]  
                                                                                                      
    ledgerTx <- submitTxConstraintsWith @Void lookups tx                                          
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx                                              
    Plutus.Contract.logInfo @String $ "Booking canceled" ++ show (getCardanoTxId ledgerTx) 
    Plutus.Contract.logInfo @String $ "Unspent UTXO output3 scriptAddress: " ++ show (getCardanoTxOutRefs ledgerTx)                                                            

endpoints :: Contract () GiftSchema Text ()
endpoints = awaitPromise (give' `select` grab') >> endpoints                                         
    where                                                                                            
    give' = endpoint @"give" give                                                                  
    grab' = endpoint @"grab" grab                                                   


-- mkSchemaDefinitions ''GiftSchema                                                                
-- mkKnownCurrencies []                                                                                 

-- | Tests
w1, w2 :: Wallet.Wallet
w1 = Wallet.knownWallet 1
w2 = Wallet.knownWallet 2

test :: IO ()
test = runEmulatorTraceIO $ do
    h1 <- activateContractWallet w1 endpoints
    h2 <- activateContractWallet w2 endpoints

    let pkh1 = Wallet.mockWalletPaymentPubKeyHash w1

        booking = BookingInfo 
                  { customer  = pkh1 
                  , aValue    = 2    -- Replace a value by 4 and the validator succed  
                  }

        param = GiveParam 
                { gAmount     = 50000000
                , bookingInfo = booking}
                

    callEndpoint @"give" h1 param
    Extras.logInfo $ "CustomerPayment Public Key Hash: " ++ show (customer $ bookingInfo param)
    void $ Emulator.waitNSlots 11
    callEndpoint @"grab" h1 0
    s <- Emulator.waitNSlots 11
    Extras.logInfo $ "End of Simulation at slot " ++ show s



