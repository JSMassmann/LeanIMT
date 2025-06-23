/-
Copyright (c) 2025 Jayde Sylvie Massmann. All rights reserved.
Thanks to Violeta Hernández Palacios for some help getting me on my feet.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.SetTheory.ZFC.Basic

inductive RudFunc : (ar: Nat) -> Type where
  | proj: Fin ar -> RudFunc ar
  | diff: Fin ar -> Fin ar -> RudFunc ar
  | pair: Fin ar -> Fin ar -> RudFunc ar
  | comp: (Fin ar2 -> RudFunc ar) -> RudFunc ar2 -> RudFunc ar
  | union: RudFunc ar -> RudFunc ar

export RudFunc (proj diff pair comp union)

attribute [instance] Classical.allZFSetDefinable

noncomputable def do_union (f: (Fin ar -> ZFSet) -> ZFSet) (x: Fin ar -> ZFSet): ZFSet :=
  match ar with
  | 0 => ∅
  | _ + 1 => ⋃₀ ZFSet.image (λz => f (λi => if i = 0 then z else x i)) (x 0)

attribute [instance] Classical.allZFSetDefinable

@[simp] lemma nullaryUnion (f: (Fin 0 -> ZFSet) -> ZFSet) (x: Fin 0 -> ZFSet) : do_union f x = ∅ := by rfl

@[simp]
theorem checkUnionElem [nz: NeZero ar] (f: (Fin ar -> ZFSet) -> ZFSet) :
    x ∈ do_union f y ↔ ∃z : ZFSet, z ∈ y 0 ∧ x ∈ f (λi => if i = 0 then z else y i) := by
  rw [do_union.eq_def]
  cases ar
  · cases nz.out rfl
  · simp

noncomputable def eval : RudFunc ar -> (Fin ar -> ZFSet) -> ZFSet
  | proj i => λx => x i
  | diff i j => λx => x i \ x j
  | pair i j => λx => {x i, x j}
  | comp inner outer => λx => eval outer λi => eval (inner i) x
  | union f => do_union (eval f)

@[simp] lemma evalProj : eval (proj i) = λx => x i := by rfl
@[simp] lemma evalDiff : eval (diff i j) = λx => x i \ x j := by rfl
@[simp] lemma evalPair : eval (pair i j) = λx => {x i, x j} := by rfl
@[simp] lemma evalComp : eval (comp inner outer) = λx => eval outer λi => eval (inner i) x := by rfl
@[simp] lemma evalUnion : eval (union f) = do_union (eval f) := by rfl

-- Converting a rud function into a higher-arity one by adding dummy variables.

def dummy (k: Nat): RudFunc ar -> RudFunc (ar + k)
  | proj i => proj (Fin.castAdd k i)
  | diff i j => diff (Fin.castAdd k i) (Fin.castAdd k j)
  | pair i j => pair (Fin.castAdd k i) (Fin.castAdd k j)
  | comp inner outer => comp (λi => dummy k (inner i)) outer
  | union f => union (dummy k f)

@[simp] lemma dummyProj : dummy k (proj i) = proj (Fin.castAdd k i) := by rfl
@[simp] lemma dummyDiff : dummy k (diff i j) = diff (Fin.castAdd k i) (Fin.castAdd k j) := by rfl
@[simp] lemma dummyPair : dummy k (pair i j) = pair (Fin.castAdd k i) (Fin.castAdd k j) := by rfl
@[simp] lemma dummyComp : dummy k (comp inner outer) = comp (λi => dummy k (inner i)) outer := by rfl
@[simp] lemma dummyUnion : dummy k (union f) = union (dummy k f) := by rfl

@[simp]
theorem dummyChangesNothing (f: RudFunc ar) (k: Nat) :
    eval (dummy k f) = λx => eval f (λi => x (Fin.castAdd k i)) := by
  induction f with
  | proj => simp
  | diff => simp
  | pair => simp
  | comp _ _ h1 h2 => sorry
  | union _ h => sorry

-- Jen71, Prop. 1.1(a) - (d); (e) is completely analogous to (d), just slightly uglier.
def rudUnion [NeZero ar] : Fin ar -> RudFunc ar := λi => comp (λ_ => proj i) (union (proj (0: Fin ar)))

def rudBinaryUnion [NeZero ar] : Fin ar -> Fin ar -> RudFunc ar := λi j => comp (λ_ => pair i j) (union (proj (0: Fin ar)))

@[simp]
theorem unionIsRud [NeZero ar] (i: Fin ar) (x: Fin ar -> ZFSet) :
    eval (rudUnion i) x = ⋃₀ x i := by
  ext; simp [rudUnion]

@[simp]
theorem binaryUnionIsRud [NeZero ar] (i j: Fin ar) (x: Fin ar -> ZFSet) :
    eval (rudBinaryUnion i j) x = (x i) ∪ (x j) := by
  ext; simp [rudBinaryUnion]

-- The only way I see to construct f(x1, x2, ..., xn) = {x1, x2, ..., xn} is via recursion on n.
def rudUnorderedTuple (ar: Nat) : RudFunc (ar + 1) :=
  match ar with
  | 0 => pair 0 0
  | ar' + 1 => comp (λ(x: Fin 2) => if x = 0 then dummy 1 (rudUnorderedTuple ar') else pair (Fin.last (ar' + 1)) (Fin.last (ar' + 1))) (rudBinaryUnion 0 1)

@[simp]
theorem unorderedTupleIsRud (x: Fin (ar + 1) -> ZFSet) :
    eval (rudUnorderedTuple ar) x = ZFSet.range x := by
  induction ar with
  | zero => ext; simp [rudUnorderedTuple]
            apply Iff.intro
            · intro h; tauto
            · intro h; obtain ⟨y, rfl⟩ := h; obtain rfl := Unique.eq_default y; rfl
  | succ _ h1 => ext; simp [rudUnorderedTuple, h1];
                 apply Iff.intro
                 · intro h2; cases h2 <;> tauto
                 · intro h2; obtain ⟨y, h2⟩ := h2
                   cases y using Fin.lastCases <;> tauto
