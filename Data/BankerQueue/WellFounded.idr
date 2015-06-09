||| Some notions relating to well-foundedness that don't require any special
||| datatypes, as there is not yet a standard set of such and it seems best
||| not to tread on anyone's toes here.
module Data.BankerQueue.WellFounded

%default total
%access public
Accessible' : (rel : a -> a -> Type) -> (x : a) -> Type
Accessible' {a} rel x = (P : a -> Type) ->
                        (step : (z : a) -> ((y : a) -> rel y z -> P y) -> P z) ->
                        P x

WellFounded' : (rel : a -> a -> Type) -> Type
WellFounded' rel = (x : _) -> Accessible' rel x

coarserAcc' : (r1,r2 : a -> a -> Type) -> (crs : (x,y : a) -> x `r1` y -> x `r2` y) ->
              (p : a) -> (accr2p : Accessible' r2 p) -> Accessible' r1 p
coarserAcc' {a} r1 r2 crs p ind P step = ind P step2
  where
    step2 : (z : a) -> ((y : a) -> r2 y z -> P y) -> P z
    step2 z g = step z (\q,qz => g q (crs q z qz))

coarserWF' : (r1,r2 : a -> a -> Type) -> (crs : (x,y : a) -> x `r1` y -> x `r2` y) ->
             (wf : WellFounded' r2) -> WellFounded' r1
coarserWF' r1 r2 crs wfr2 x = coarserAcc' r1 r2 crs x (wfr2 x)


||| ``r `On` f`` is the inverse image of `r` under `f`.
On : (r : b -> b -> Type) -> (f : a -> b) -> (a -> a -> Type)
On {a} rb f x y = rb (f x) (f y)

||| If the image of an element under a function is accessible relative
||| to a relation, then the element is accessible under the inverse
||| image of the relation.
inverseImageAcc' : {a,b : Type} -> (rb : b -> b -> Type) -> (f : a -> b) ->
                   (x : a) -> Accessible' rb (f x) -> Accessible' (rb `On` f) x
inverseImageAcc' {a} {b} rb f m accm P step = accm (invPred P) step2 m Refl
  where
    invPred : (p : a -> Type) -> b -> Type
    invPred p y = (x : a) -> f x = y -> p x

    step2 : (z : b) ->
            ((y : b) -> rb y z -> invPred P y) -> invPred P z
    step2 z g x fxz = step x (\q, fyfz => let foo = g (f q) (replace {P=rb (f q)} fxz fyfz) in foo q Refl)

||| The inverse image of a well-founded relation under a function is
||| well-founded.
inverseImageWF' : {a,b : Type} -> (rb : b -> b -> Type) -> (f : a -> b) ->
                  WellFounded' rb -> WellFounded' (rb `On` f)
inverseImageWF' rb f wfr x = inverseImageAcc' rb f x (wfr (f x))

NatSucc : Nat -> Nat -> Type
NatSucc m n = S m = n

-- We would write natSuccWF' : WellFounded' NatSucc, but for some strange reason
-- the totality checker reports missing cases if we do that.
natSuccWF' : (x : Nat) ->
             (P : Nat -> Type) ->
             (step : (z : Nat) -> ((y : Nat) -> NatSucc y z -> P y) -> P z) ->
             P x
natSuccWF' Z P step = step Z (\y,ab => absurd (sym ab))
natSuccWF' (S n) P step = step (S n) ind
  where
    ind : (y : Nat) -> (S y = S n) -> P y
    ind y yn = rewrite (succInjective y n yn) in  natSuccWF' n P step
