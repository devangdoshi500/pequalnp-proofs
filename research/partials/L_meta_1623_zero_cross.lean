import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1623_aux.EnvelopeAlgebra

def envelope {α : Type} (b : Bool) (f : α → Bool) (Y : Finset α) : Bool :=
  b || decide (∃ j ∈ Y, f j = true)

lemma envelope_or {α : Type} (a b : Bool) (f g : α → Bool) (Y : Finset α) :
    envelope (a || b) (fun j => f j || g j) Y =
      (envelope a f Y || envelope b g Y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [envelope, Bool.or_eq_true, decide_eq_true_eq]
  aesop

lemma envelope_constant_left {α : Type} (a b : Bool) (f : α → Bool) (Y : Finset α) :
    envelope (a && b) (fun j => a && f j) Y = (a && envelope b f Y) := by
  cases a <;> simp [envelope]

lemma envelope_constant_right {α : Type} (a b : Bool) (f : α → Bool) (Y : Finset α) :
    envelope (a && b) (fun j => f j && b) Y = (envelope a f Y && b) := by
  cases b <;> simp [envelope]

lemma envelope_constant {α : Type} (b : Bool) (Y : Finset α) :
    envelope b (fun _ => b) Y = b := by
  cases b <;> simp [envelope]

lemma envelope_and_zero_left {α : Type} (a b : Bool) (f g : α → Bool)
    (Y : Finset α) (hf : ∀ j, f j = a) :
    (envelope a f Y && envelope b g Y) =
      envelope (a && b) (fun j => f j && g j) Y := by
  have hfun : f = fun _ => a := funext hf
  subst f
  rw [envelope_constant, envelope_constant_left]

lemma envelope_and_zero_right {α : Type} (a b : Bool) (f g : α → Bool)
    (Y : Finset α) (hg : ∀ j, g j = b) :
    (envelope a f Y && envelope b g Y) =
      envelope (a && b) (fun j => f j && g j) Y := by
  have hfun : g = fun _ => b := funext hg
  subst g
  rw [envelope_constant, envelope_constant_right]

end PEqualNP.Outside.L_meta_1623_aux.EnvelopeAlgebra


namespace PEqualNP.Outside.L_meta_1623_aux
open PEqualNP.CircuitLowerBounds

lemma max_fold_zero (l : List ℕ) (h : l.foldr max 0 = 0) :
    ∀ a ∈ l, a = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons] at h
    have ha : a = 0 := by omega
    have hl : l.foldr max 0 = 0 := by omega
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact ih hl b hb

lemma gate_zero_inputs (g : Gate) (d : List ℕ) (h : g.lineDegree d = 0) :
    ∀ i ∈ g.inputs, d.getD i 0 = 0 := by
  classical
  unfold Gate.lineDegree at h
  split_ifs at h with hop
  · intro i hi
    have hall := List.sum_eq_zero_iff.mp h
    exact hall _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro i hi
    exact max_fold_zero _ h _ (List.mem_map.mpr ⟨i, hi, rfl⟩)

lemma gate_zero_value (g : Gate) (d : List ℕ) (a b : List Bool)
    (h : ∀ i, d.getD i 0 = 0 → a.getD i false = b.getD i false)
    (hz : g.lineDegree d = 0) :
    g.op.eval (g.inputs.map (fun i => a.getD i false)) =
      g.op.eval (g.inputs.map (fun i => b.getD i false)) := by
  congr 1
  exact List.map_congr_left (fun i hi => h i (gate_zero_inputs g d hz i hi))

lemma append_zero_invariant (d : List ℕ) (a b : List Bool)
    (da : d.length = a.length) (db : d.length = b.length)
    (h : ∀ i, d.getD i 0 = 0 → a.getD i false = b.getD i false)
    (dv : ℕ) (av bv : Bool) (hv : dv = 0 → av = bv) :
    ∀ i, (d ++ [dv]).getD i 0 = 0 →
      (a ++ [av]).getD i false = (b ++ [bv]).getD i false := by
  intro i hi
  by_cases ilt : i < d.length
  · rw [List.getD_append _ _ _ _ ilt] at hi
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), ← da, ← db]
    by_cases heq : i - d.length = 0
    · simp only [heq, List.getD_cons_zero] at hi ⊢
      exact hv hi
    · obtain ⟨j, hj⟩ : ∃ j, i - d.length = j + 1 := ⟨i - d.length - 1, by omega⟩
      simp [hj]

lemma fold_zero_invariant (gs : List Gate) (d : List ℕ) (a b : List Bool)
    (da : d.length = a.length) (db : d.length = b.length)
    (h : ∀ i, d.getD i 0 = 0 → a.getD i false = b.getD i false) :
    ∀ i, (gs.foldl (fun ds g => ds ++ [g.lineDegree ds]) d).getD i 0 = 0 →
      (gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map (fun j => vs.getD j false))]) a).getD i false =
      (gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map (fun j => vs.getD j false))]) b).getD i false := by
  induction gs generalizing d a b with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp [da]
    · simp [db]
    · exact append_zero_invariant d a b da db h _ _ _ (gate_zero_value g d a b h)

lemma wire_zero_independent (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i.val ∉ marked → x i = y i)
    (i : ℕ) (hz : (C.lineDegrees n marked).getD i 0 = 0) :
    (C.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn y)).getD i false := by
  apply fold_zero_invariant C.gates
      ((List.range n).map (fun j => if j ∈ marked then 1 else 0))
      (List.ofFn x) (List.ofFn y) (by simp) (by simp) ?_ i hz
  intro j hj
  by_cases hjn : j < n
  · have hjmark : j ∉ marked := by
      intro hm
      simp [List.getD_eq_getElem?_getD, hjn, hm] at hj
    have hv := hxy ⟨j, hjn⟩ hjmark
    simpa [List.getD_eq_getElem?_getD, hjn] using hv
  · rw [List.getD_eq_default, List.getD_eq_default]
    all_goals simp; omega

end PEqualNP.Outside.L_meta_1623_aux

namespace PEqualNP.Outside.L_meta_1623_aux
open PEqualNP.CircuitLowerBounds EnvelopeAlgebra

lemma gate_envelope {α : Type} (g : Gate) (d : ℕ → ℕ)
    (b e : ℕ → Bool) (f : α → ℕ → Bool) (Y : Finset α)
    (hzero : ∀ i, d i = 0 → ∀ j, f j i = b i)
    (henv : ∀ i, e i = envelope (b i) (fun j => f j i) Y)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2)
    (hcross : g.op = GateOp.and → g.inputs.length = 2 →
      ∃ i ∈ g.inputs, d i = 0) :
    g.op.eval (g.inputs.map e) = envelope (g.op.eval (g.inputs.map b))
      (fun j => g.op.eval (g.inputs.map (f j))) Y := by
  rcases g with ⟨op, ins⟩
  simp only at hop hlen hcross ⊢
  have shapes : ins = [] ∨ (∃ i, ins = [i]) ∨ ∃ i j, ins = [i,j] := by
    cases ins with
    | nil => exact Or.inl rfl
    | cons i ins =>
      cases ins with
      | nil => exact Or.inr (Or.inl ⟨i,rfl⟩)
      | cons j ins =>
        cases ins with
        | nil => exact Or.inr (Or.inr ⟨i,j,rfl⟩)
        | cons k ins => simp at hlen
  rcases shapes with rfl | ⟨i,rfl⟩ | ⟨i,j,rfl⟩
  · rcases hop with rfl | rfl <;> simp [GateOp.eval, envelope]
  · rcases hop with rfl | rfl <;> simpa [GateOp.eval] using henv i
  · rcases hop with rfl | rfl
    · obtain ⟨v,hv,hz⟩ := hcross rfl rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hv | hv
      · simpa [GateOp.eval, henv] using
          envelope_and_zero_left (b i) (b j) (fun a => f a i) (fun a => f a j) Y (hzero i (by simpa [hv] using hz))
      · simpa [GateOp.eval, henv] using
          envelope_and_zero_right (b i) (b j) (fun a => f a i) (fun a => f a j) Y (hzero j (by simpa [hv] using hz))
    · simpa [GateOp.eval, henv] using
        (envelope_or (b i) (b j) (fun a => f a i) (fun a => f a j) Y).symm

end PEqualNP.Outside.L_meta_1623_aux

namespace PEqualNP.Outside.L_meta_1623_aux
open PEqualNP.CircuitLowerBounds EnvelopeAlgebra

lemma append_envelope {α : Type} (b v : List Bool) (f : α → List Bool) (Y : Finset α)
    (hvlen : v.length = b.length) (hflen : ∀ j, (f j).length = b.length)
    (henv : ∀ i, v.getD i false = envelope (b.getD i false) (fun j => (f j).getD i false) Y)
    (bv vv : Bool) (fv : α → Bool)
    (hval : vv = envelope bv fv Y) :
    ∀ i, (v ++ [vv]).getD i false =
      envelope ((b ++ [bv]).getD i false)
        (fun j => (f j ++ [fv j]).getD i false) Y := by
  intro i
  by_cases hi : i < b.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    have hf : (fun j => (f j ++ [fv j]).getD i false) = fun j => (f j).getD i false := by
      funext j
      exact List.getD_append _ _ _ _ (by rw [hflen]; exact hi)
    rw [hf]
    exact henv i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hvlen]
    have hf : (fun j => (f j ++ [fv j]).getD i false) =
        fun j => [fv j].getD (i - b.length) false := by
      funext j
      rw [List.getD_append_right _ _ _ _ (by rw [hflen]; omega), hflen]
    rw [hf]
    by_cases he : i - b.length = 0
    · simpa [he] using hval
    · obtain ⟨k, hk⟩ : ∃ k, i - b.length = k + 1 := ⟨i - b.length - 1, by omega⟩
      simp [hk, envelope]

def noCrossFrom : List Gate → List ℕ → Prop
  | [], _ => True
  | g :: gs, d =>
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧
    (g.op = GateOp.and → g.inputs.length = 2 → ∃ i ∈ g.inputs, d.getD i 0 = 0) ∧
    noCrossFrom gs (d ++ [g.lineDegree d])

def boolStep (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))]

def degreeStep (d : List ℕ) (g : Gate) : List ℕ :=
  d ++ [g.lineDegree d]

lemma fold_envelope {α : Type} (gs : List Gate) (d : List ℕ)
    (b v : List Bool) (f : α → List Bool) (Y : Finset α)
    (hgood : noCrossFrom gs d)
    (hdlen : d.length = b.length) (hvlen : v.length = b.length)
    (hflen : ∀ j, (f j).length = b.length)
    (hzero : ∀ j i, d.getD i 0 = 0 → (f j).getD i false = b.getD i false)
    (henv : ∀ i, v.getD i false = envelope (b.getD i false) (fun j => (f j).getD i false) Y) :
    ∀ i, (gs.foldl boolStep v).getD i false =
      envelope ((gs.foldl boolStep b).getD i false)
        (fun j => (gs.foldl boolStep (f j)).getD i false) Y := by
  induction gs generalizing d b v f with
  | nil => exact henv
  | cons g gs ih =>
    rcases hgood with ⟨hop, hlen, hcross, htail⟩
    simp only [List.foldl_cons]
    apply ih (d := degreeStep d g) (f := fun j => boolStep (f j) g)
    · exact htail
    · simp [degreeStep, boolStep, hdlen]
    · simp [boolStep, hvlen]
    · intro j; simp [boolStep, hflen j]
    · intro j
      exact append_zero_invariant d (f j) b (by rw [hflen j]; exact hdlen) hdlen
        (hzero j) _ _ _ (gate_zero_value g d (f j) b (hzero j))
    · apply append_envelope b v f Y hvlen hflen henv
      exact gate_envelope g (fun i => d.getD i 0) (fun i => b.getD i false)
        (fun i => v.getD i false) (fun j i => (f j).getD i false) Y
        (fun i hi j => hzero j i hi) henv hop hlen hcross

end PEqualNP.Outside.L_meta_1623_aux

namespace PEqualNP.Outside.L_meta_1623_aux
open PEqualNP.CircuitLowerBounds EnvelopeAlgebra

lemma degree_fold_prefix (gs : List Gate) (d : List ℕ) :
    ∃ t : List ℕ, gs.foldl degreeStep d = d ++ t := by
  induction gs generalizing d with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (degreeStep d g)
    exact ⟨g.lineDegree d :: t, by simpa [degreeStep, List.append_assoc] using ht⟩

lemma degree_fold_getD (gs : List Gate) (d : List ℕ) (i : ℕ) (hi : i < d.length) :
    (gs.foldl degreeStep d).getD i 0 = d.getD i 0 := by
  obtain ⟨t, ht⟩ := degree_fold_prefix gs d
  rw [ht, List.getD_append _ _ _ _ hi]

lemma noCrossFrom_of_global (gs : List Gate) (d : List ℕ)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hread : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < d.length + j)
    (hcross : ∀ g ∈ gs, g.op = GateOp.and → g.inputs.length = 2 →
      ∃ i ∈ g.inputs, (gs.foldl degreeStep d).getD i 0 = 0) :
    noCrossFrom gs d := by
  induction gs generalizing d with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hmono g (by simp)
    refine ⟨hop, hlen, ?_, ?_⟩
    · intro hand htwo
      obtain ⟨i, hi, hz⟩ := hcross g (by simp) hand htwo
      refine ⟨i, hi, ?_⟩
      have hib : i < d.length := by simpa using hread 0 (by simp) i (by simpa using hi)
      rw [degree_fold_getD (g :: gs) d i hib] at hz
      exact hz
    · apply ih (d := degreeStep d g)
      · intro g' hg'
        exact hmono g' (List.mem_cons_of_mem g hg')
      · intro j hj i hi
        have hh := hread (j + 1) (by simp; omega) i (by simpa using hi)
        simp only [degreeStep, List.length_append, List.length_singleton]
        omega
      · intro g' hg'
        exact hcross g' (List.mem_cons_of_mem g hg')

end PEqualNP.Outside.L_meta_1623_aux

namespace PEqualNP.Outside.L_meta_1623_aux
open PEqualNP.CircuitLowerBounds EnvelopeAlgebra

lemma getD_ofFn_lt {N : ℕ} (f : Fin N → Bool) (i : ℕ) (hi : i < N) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma input_envelope (n m : ℕ) (x : Fin n → Bool) (Y : Finset (Fin m)) (i : Fin (n + m)) :
    Fin.append x (fun l => decide (l ∈ Y)) i =
      envelope (Fin.append x (fun _ => false) i)
        (fun j => Fin.append x (fun l => decide (l = j)) i) Y := by
  refine Fin.addCases ?_ ?_ i
  · intro p
    simpa using (envelope_constant (x p) Y).symm
  · intro l
    simp [envelope]

lemma circuit_envelope_noCross (n m : ℕ) (C : Circuit)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hread : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C)
    (hcross : ∀ j < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 →
      ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0)
    (x : Fin n → Bool) (Y : Finset (Fin m)) :
    PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) =
      envelope (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)))
        (fun j => PEqualNP.MetaComplexity.circuitFun (n + m) C
          (Fin.append x (fun l => decide (l = j)))) Y := by
  let d := (List.range (n + m)).map (fun j => if j ∈ Finset.Ico n (n + m) then 1 else 0)
  let b := List.ofFn (Fin.append x (fun _ : Fin m => false))
  let v := List.ofFn (Fin.append x (fun l : Fin m => decide (l ∈ Y)))
  let f := fun j : Fin m => List.ofFn (Fin.append x (fun l : Fin m => decide (l = j)))
  have hdlen : d.length = n + m := by simp [d]
  have hblen : b.length = n + m := by simp [b]
  have hvlen : v.length = b.length := by simp [v, b]
  have hflen : ∀ j, (f j).length = b.length := by intro j; simp [f, b]
  have hgood : noCrossFrom C.gates d := by
    apply noCrossFrom_of_global
    · intro g hg
      obtain ⟨hop, hlen⟩ := hmono g hg
      exact ⟨by simpa using hop, hlen⟩
    · simpa only [hdlen, PEqualNP.MetaComplexity.NestedCover.ReadsBack,
      PEqualNP.MetaComplexity.NestedCover.gateAt] using hread
    · intro g hg hand htwo
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
      obtain ⟨i, hi, hz⟩ := hcross j hj (by simpa [hget] using hand) (by simpa [hget] using htwo)
      exact ⟨i, by simpa [hget] using hi, hz⟩
  have hzero : ∀ j i, d.getD i 0 = 0 → (f j).getD i false = b.getD i false := by
    intro j i hi
    by_cases hin : i < n + m
    · have himark : i ∉ Finset.Ico n (n + m) := by
        intro hm
        simp [d, List.getD_eq_getElem?_getD, hin] at hi
        have hmlo := (Finset.mem_Ico.mp hm).1
        omega
      have hip : i < n := by
        have hnot : ¬ (n ≤ i ∧ i < n + m) := by simpa using himark
        omega
      dsimp only [f, b]
      rw [getD_ofFn_lt _ i hin, getD_ofFn_lt _ i hin]
      change Fin.append x _ (Fin.castAdd m ⟨i, hip⟩) = Fin.append x _ (Fin.castAdd m ⟨i, hip⟩)
      rw [Fin.append_left, Fin.append_left]
    · simp [f, b, List.getD_eq_getElem?_getD, hin]
  have henv : ∀ i, v.getD i false = envelope (b.getD i false) (fun j => (f j).getD i false) Y := by
    intro i
    by_cases hin : i < n + m
    · dsimp only [v, b, f]
      simp only [getD_ofFn_lt _ i hin]
      exact input_envelope n m x Y ⟨i, hin⟩
    · simp [v, b, f, List.getD_eq_getElem?_getD, hin, envelope]
  exact fold_envelope C.gates d b v f Y hgood (by omega) hvlen hflen hzero henv C.output

end PEqualNP.Outside.L_meta_1623_aux

namespace PEqualNP.Outside.L_meta_1623_aux
open PEqualNP.CircuitLowerBounds EnvelopeAlgebra

lemma bounded_index_ncard (s : Set ℕ) (N : ℕ) (h : ∀ j ∈ s, j < N) : s.ncard ≤ N := by
  have hs : s ⊆ ↑(Finset.range N) := by
    intro j hj
    exact Finset.mem_range.mpr (h j hj)
  simpa using Set.ncard_le_ncard hs (Finset.finite_toSet _)

lemma noCross_of_zero_count (n m : ℕ) (C : Circuit)
    (hcount : Set.ncard {j : ℕ | j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧
      ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ 0) :
    ∀ j < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 →
      ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0 := by
  classical
  let S := {j : ℕ | j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧
      ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0}
  have hfin : S.Finite := (Finset.finite_toSet (Finset.range C.gates.length)).subset
    (by intro j hj; simpa using hj.1)
  have hempty : S = ∅ := (Set.ncard_eq_zero hfin).mp (Nat.eq_zero_of_le_zero hcount)
  intro j hj hand htwo
  by_contra hn
  have hpos : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 := by
    intro i hi
    have hz : (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 ≠ 0 := by
      intro hz; exact hn ⟨i, hi, hz⟩
    omega
  have hmem : j ∈ S := ⟨hj, hand, htwo, hpos⟩
  simp [hempty] at hmem

end PEqualNP.Outside.L_meta_1623_aux

namespace PEqualNP.Outside.L_meta_1623_aux
open PEqualNP.CircuitLowerBounds

lemma zero_cross_case : ∀ (n m s : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ 0 → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * 0 + 3) * s + 12 * 0 ^ 2 * m + 7 * 0 * m + 6 * 0 ^ 2 + 2 * 0 ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + 0 * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true)) := by
  intro n m s C hm hr hs hc
  have hnc := noCross_of_zero_count n m C hc
  refine ⟨C, hm, hr, hnc, ?_, ?_, ?_⟩
  · simp only [zero_mul, mul_zero, zero_add, add_zero, zero_pow (by decide : 2 ≠ 0)]
    omega
  · have hb := bounded_index_ncard
      {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0}
      C.gates.length (by intro j hj; exact hj.1)
    simp only [zero_mul, add_zero]
    exact hb.trans hs
  · intro x Y
    apply Bool.eq_iff_iff.mpr
    have he := Bool.eq_iff_iff.mp (circuit_envelope_noCross n m C hm hr hnc x Y)
    simpa only [EnvelopeAlgebra.envelope, Bool.or_eq_true, decide_eq_true_eq] using he

end PEqualNP.Outside.L_meta_1623_aux

#print axioms PEqualNP.Outside.L_meta_1623_aux.zero_cross_case
