{-|
Module      : Main
Description : Translation of Rabin to parity automata using Index Appearance Records
Copyright   : Clara Waldmann, 2016

-}
module Main where

import System.Exit ( exitFailure, exitSuccess )
import qualified  Data.Text.IO as IOT
import qualified Options.Applicative as OA
import Options.Applicative.Extra
import Data.Attoparsec.Text

import OmegaAutomata.Hoa as H
import OmegaAutomata.Automata
import qualified IAR as IAR
import qualified IAR_optimized as Opt 
import qualified IAR_Streett as Streett
import AR


data ArgOpts = ArgOpts
    { streett :: Bool
    , opt :: Bool
    }

argOpts :: OA.Parser ArgOpts
argOpts = ArgOpts
    <$>     OA.switch 
                (OA.long "streett"
                OA.<> OA.help "use IAR procedure for Streett automata"
                )
        <*> OA.switch 
                (OA.long "opt"
                OA.<> OA.help "Use improvements (SCC decomposition and finding a good initial state for each SCC)"
                )
        


execute :: (AR ar, Ord (ar q), Show (ar q), Ord q )=> ArgOpts -> (DRA q (Maybe LabelExpr) l -> DPA (ar q) (Maybe LabelExpr) Int) -> DRA q (Maybe LabelExpr) l -> HOA
execute args rab2par dra =
    let dpa =
            if opt args 
               then Opt.rabin2parity rab2par dra
               else rab2par dra
    in dpaToHoa dpa
    
                                        
                    
main :: IO ()
main = do
  args <- execParser $
        OA.info (OA.helper <*> argOpts) 
            (OA.fullDesc OA.<> OA.progDesc "translation of Rabin automata to parity automata using Index Appearance Records" OA.<> OA.header "IAR-exe")
  
  IOT.getContents >>= (\s -> do
        let p = parseOnly parseHoa s 
        case p of
           Left s   -> do putStrLn "\nParse              Failed...\n"
                          putStrLn s
                          exitFailure
           Right hdra -> do
                let props = [AP b | (AP b) <- H.header hdra]
                    dra = hoaToDRA hdra
                            
                    hdpa =  if streett args
                                then execute args 
                                    (rabin2parity :: Ord q => 
                                        DRA q (Maybe LabelExpr) l 
                                     -> DPA (Streett.SIAR q) (Maybe LabelExpr) Int) 
                                      dra
                                else execute args 
                                    (rabin2parity :: Ord q => 
                                        DRA q (Maybe LabelExpr) l 
                                     -> DPA (IAR.IAR q) (Maybe LabelExpr) Int) 
                                      dra
                
                putStrLn $ toHoa hdpa
                exitSuccess

        )


