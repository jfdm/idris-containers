||| Example Queries over AList implemented graphs.
|||
||| TODO make query higher-order.
module Data.Graph.AList.Query

import Effects
import Effect.State
import Effect.StdIO

import Data.Graph.AList

import Data.Queue
import Data.Stack

%access public

-- --------------------------------------------------------------------- [ BFS ]
||| The effects used in a BFS.
BfsEffs : List EFFECT
BfsEffs = [ 'next ::: STATE (Queue Node),
            'seen ::: STATE (List Node),
            STDIO]

||| Traverse the given graph using a BFS, printing the visited nodes
||| in order of visit.
private
doTraceBFS : (Ord n, Show n) => Graph n e -> Eff () BfsEffs
doTraceBFS g = do
   q <- 'next :- get
   case popQ q of
     Nothing         => pure () -- Stop if all nodes have been traversed.
     Just (curr, q') => do
       'next :- put q'
       -- Do the thing we do at the nodes.
       putStrLn $ show curr

       -- Move on
       let es = getSuccs curr g
       doMoves es

       -- Repeat
       doTraceBFS g
  where
    doMove : Node -> Eff () BfsEffs
    doMove n = do
      visited <- 'seen :- get
      case elem n visited of
        True => pure ()
        False => do
          'seen :- update (\xs => [n] ++ xs)
          'next :- update (\xs => pushQ n xs)

    doMoves : Maybe (List Node) -> Eff () BfsEffs
    doMoves Nothing = pure ()
    doMoves (Just Nil) = pure ()
    doMoves (Just (e::es)) = do
       doMove e
       doMoves (Just es)

||| Traverse the given graph using a BFS, printing the visited nodes
||| in order of visit.
traceBfsIO : (Ord v, Show v) => Node -> Graph v e -> IO ()
traceBfsIO n g = runInit ['next := initQ n, 'seen := List.Nil, ()] $ doTraceBFS g

-- --------------------------------------------------------------------- [ DFS ]
||| The Effects used in a DFS.
DfsEffs : List EFFECT
DfsEffs = [ 'next ::: STATE (Stack Node),
            'seen ::: STATE (List Node),
            STDIO]

||| Traverse the given graph using a DFS, printing the visited nodes
||| in order of visit.
doTraceDFS : (Ord n, Show n) => Graph n e -> Eff () DfsEffs
doTraceDFS g = do
    s <- 'next :- get
    case popS s of
      Nothing         => pure ()
      Just (curr, s') => do
        'next :- put s'
        visited <- 'seen :- get
        case elem curr visited of
          True  => pure ()
          False => do
            putStrLn $ show curr
            let es = getSuccs curr g
            'seen :- update (\xs => [curr] ++ xs)
            'next :- update (\xs => pushSThings (fromMaybe Nil es) s)
            doTraceDFS g

||| Traverse the given graph using a DFS, printing the visited nodes
||| in order of visit.
traceDfsIO : (Ord v, Show v) => Node -> Graph v e -> IO ()
traceDfsIO n g = runInit ['next := initS n, 'seen := List.Nil, ()] $ doTraceDFS g
-- --------------------------------------------------------------------- [ EOF ]
