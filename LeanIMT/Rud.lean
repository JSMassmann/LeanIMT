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

-- Often, ar = 0 requires no special treatment, so we don't bother banning it outright.
-- There's no need to use tactics here.
theorem no_nullary_rudfuncs : RudFunc 0 -> False
  | proj i => i.elim0
  | diff i _ => i.elim0
  | pair i _ => i.elim0
  | comp inner outer => by rename_i ar2; cases ar2
                           · exact no_nullary_rudfuncs outer
                           · exact no_nullary_rudfuncs (inner 0)
  | union f => no_nullary_rudfuncs f
termination_by sorry

attribute [instance] Classical.allZFSetDefinable

noncomputable def do_union (f: (Fin ar -> ZFSet) -> ZFSet) (x: Fin ar -> ZFSet): ZFSet :=
  match ar with
  | 0 => ∅
  | _ + 1 => ⋃₀ ZFSet.image (λz => f (λi => if i = 0 then z else x i)) (x 0)

@[simp] lemma nullaryUnion (f: (Fin 0 -> ZFSet) -> ZFSet) (x: Fin 0 -> ZFSet) : do_union f x = ∅ := by rfl

@[simp]
theorem mem_do_union [nz: NeZero ar] (f: (Fin ar -> ZFSet) -> ZFSet) :
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
theorem eval_dummy_eq_eval (f: RudFunc ar) (k: Nat) :
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
theorem eval_rudunion_eq_union [NeZero ar] (i: Fin ar) (x: Fin ar -> ZFSet) :
    eval (rudUnion i) x = ⋃₀ x i := by
  ext; simp [rudUnion]

@[simp]
theorem eval_rudbinaryunion_eq_binaryunion [NeZero ar] (i j: Fin ar) (x: Fin ar -> ZFSet) :
    eval (rudBinaryUnion i j) x = (x i) ∪ (x j) := by
  ext; simp [rudBinaryUnion]

-- The only way I see to construct f(x1, x2, ..., xn) = {x1, x2, ..., xn} is via recursion on n.
def rudUnorderedTuple (ar: Nat) : RudFunc (ar + 1) :=
  match ar with
  | 0 => pair 0 0
  | ar' + 1 => comp (λ(x: Fin 2) => if x = 0 then dummy 1 (rudUnorderedTuple ar') else pair (Fin.last (ar' + 1)) (Fin.last (ar' + 1))) (rudBinaryUnion 0 1)

@[simp]
theorem eval_rudunorderedtuple_eq_range (x: Fin (ar + 1) -> ZFSet) :
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

def RudRelation (R: (Fin ar -> ZFSet) -> Prop) : Prop :=
  ∃f: RudFunc ar, ∀x: Fin ar -> ZFSet, R x = true ↔ ZFSet.Nonempty (eval f x)

theorem no_nullary_rudrelations (R: (Fin 0 -> ZFSet) -> Prop) : RudRelation R -> False := by
  intro h
  rw [RudRelation] at h
  obtain ⟨r, h⟩ := h
  exfalso
  exact no_nullary_rudfuncs r

-- Jen71, Prop. 1.2(a) - (f). The proofs of (g), (h) are incorrect.
theorem not_mem_is_rud : RudRelation (λ(x: Fin 2 -> ZFSet) => x 0 ∉ x 1) := by
  rw [RudRelation]

  -- f(x, y) = {x} \ y is nonempty iff x ∉ y.
  let inner : Fin 2 -> RudFunc 2 := λx => if x = 0 then proj 1 else pair 0 0;
  let f := comp inner (diff 1 0)
  use f
  simp [f, inner, ZFSet.nonempty_def]

theorem rudfunc_by_if_else (R: (Fin ar -> ZFSet) -> Prop) (f: RudFunc ar) [∀x: Fin ar -> ZFSet, Decidable (R x)] :
    RudRelation R -> ∃g: RudFunc ar, ∀x: Fin ar -> ZFSet, eval g x = if R x then eval f x else ∅ := by
  intro h; rw [RudRelation] at h; obtain ⟨r, h⟩ := h; simp at h
  cases ar
  · exfalso; exact no_nullary_rudfuncs f
    -- g(x) = U[z in r(x)] f(x). The z doesn't matter; this is nonempty iff both r(x) and f(x) are.
  · let g := comp (λ(i: Fin 2) => if i = 0 then r else f) (union (proj 1))
    use g; intro x; ext; split
    · simp [g]; intro; simp [← ZFSet.nonempty_def, ← h]; tauto
    · simp [g]; intro _ h2;
      apply ZFSet.nonempty_of_mem at h2; rw [← h] at h2; tauto

-- f x = {x \ x} = {{}} (von Neumann ordinal {0} = 1).
def const_one [NeZero ar] : RudFunc ar := comp (λ(_: Fin 1) => diff 0 0) (pair 0 0)

theorem neg_rud_is_rud (R: (Fin ar -> ZFSet) -> Prop) [∀x: Fin ar -> ZFSet, Decidable (R x)]:
    RudRelation R -> RudRelation λx => ¬R x := by
  intro h
  cases ar
  · exfalso; exact no_nullary_rudrelations R h
  · let h2 := rudfunc_by_if_else R const_one
    apply h2 at h; obtain ⟨r, h⟩ := h
    -- f(x) = 1 \ r(x). r always takes value either 0 or 1, hence f(x) is nonempty iff r(x) is empty.
    let f := comp (λ(i: Fin 2) => if i = 0 then r else const_one) (diff 1 0)
    simp [RudRelation]; use f; intro x; apply Iff.intro
    · intro h3; simp [f, const_one, h, h3, ZFSet.nonempty_def];
    · simp [f, const_one, h, ZFSet.nonempty_def];
      intro h3; intro h4; simp [h4] at h3

-- We don't actually need "for all x, there is i s.t. R(i, x)", because we phrase rud_runc_piecewise by assuming
-- this, to avoid speaking about "the unique i s.t..." and relying on disjointness for uniqueness of the one we've
-- already picked.
def RudRelationPartition (R: Fin n -> (Fin ar -> ZFSet) -> Prop) : Prop :=
  (∀i: Fin n, RudRelation (λx => R i x)) ∧
  (∀i j: Fin n, ∀x: Fin ar -> ZFSet, i ≠ j → ¬(R i x ∧ R j x))

-- Clearly, eval union_range = λx => ⋃₀ ZFSet.range x.
-- We def this because inlining it seems to confuse the type checker.
def union_range : RudFunc (ar + 1) := comp (λ(_: Fin 1) => rudUnorderedTuple ar) (rudUnion 0)

theorem rudfunc_piecewise (R: Fin n -> (Fin ar -> ZFSet) -> Prop) (f: Fin n -> RudFunc ar) [∀i: Fin n, ∀x: Fin ar -> ZFSet, Decidable (R i x)]:
    RudRelationPartition R -> ∃g: RudFunc ar, ∀x, R i x → eval g x = eval (f i) x := by
  cases ar
  · cases n
    · exact i.elim0
    · exfalso; exact no_nullary_rudfuncs (f 0)
  · cases n
    · exact i.elim0
    · intro h; rw [RudRelationPartition] at h
      -- p(i, x) tells us there is some rud function that evaluates to f(i, x) when R(i, x) and {} else.
      -- g(i, x) picks some such function; it can probably be made constructive in the future. h4(i) tells us
      -- that g(i, x) indeed has this property.

      let p := λi => rudfunc_by_if_else (R i) (f i) (h.left i)
      let g := comp (λi => Classical.choose (p i)) union_range
      let h4 := λi => Classical.choose_spec (p i)
      use g; intro x h2; ext; simp [union_range, g]; apply Iff.intro
      · intro h3; obtain ⟨a, h3⟩ := h3
        specialize h4 a x
        by_cases hai: a = i
        · simp [hai, h2] at h4; simp [← h4]; simp [← hai]; exact h3
        · let hdis := h.right; specialize hdis a i x hai
          simp [h2] at hdis; simp [hdis] at h4; simp [h4] at h3
      · intro h3
        specialize h4 i x; simp [h2] at h4; rw [← h4] at h3
        use i

theorem rud_downset_is_rud (R: (Fin ar -> ZFSet) -> Prop) [∀x: Fin ar -> ZFSet, Decidable (R x)] [NeZero ar] :
    RudRelation R -> ∃g: RudFunc ar, ∀x: Fin ar -> ZFSet, ∀z: ZFSet, z ∈ eval g x ↔ z ∈ x 0 ∧ R (λi => if i = 0 then z else x i) := by
  intro h
  let h2 := rudfunc_by_if_else R (pair 0 0) h
  obtain ⟨g, h2⟩ := h2; use union g; intro x z
  apply Iff.intro
  · intro h3; simp [h2] at h3
    obtain ⟨y, h3⟩ := h3
    by_cases hr: R (λi => if i = 0 then y else x i)
    · simp [hr] at h3; simp [h3]; exact hr
    · simp [hr] at h3
  · intro h3; simp [h2]; use z; simp [h3.right]; exact h3.left
