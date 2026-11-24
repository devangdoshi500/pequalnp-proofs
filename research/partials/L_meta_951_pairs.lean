import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951_aux
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

lemma fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map (fun i => w.getD i false)) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix C.gates x
  change (C.gates.foldl step x).getD i false = _
  rw [ht, List.getD_append _ _ _ _ hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix C.gates x
  change (C.gates.foldl step x).length = _
  rw [ht]
  simp [hl]

lemma singleton_eval (n m : ℕ) (S : Fin m → Finset (Fin n))
    (gs : List Gate) (out : Fin m → ℕ)
    (hc : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true))
    (w : Fin m) (v : Fin n) :
    Circuit.eval ⟨gs, out w⟩ (List.ofFn (fun z => decide (z = v))) = decide (v ∈ S w) := by
  rw [hc]
  simp

lemma output_injective (n m : ℕ) (S : Fin m → Finset (Fin n))
    (hsize : ∀ w, 2 ≤ (S w).card)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ)
    (hc : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    Function.Injective out := by
  intro i j hout
  by_contra hij
  have hsets : S i = S j := by
    apply Finset.ext
    intro v
    have he : Circuit.eval ⟨gs, out i⟩ (List.ofFn (fun z => decide (z = v))) =
        Circuit.eval ⟨gs, out j⟩ (List.ofFn (fun z => decide (z = v))) := by rw [hout]
    rw [singleton_eval n m S gs out hc i v, singleton_eval n m S gs out hc j v] at he
    simpa only [decide_eq_true_eq] using Bool.eq_iff_iff.mp he
  have hh := hinter i j hij
  rw [hsets, Finset.inter_self] at hh
  have := hsize j
  omega

lemma output_is_gate (n m : ℕ) (S : Fin m → Finset (Fin n))
    (hsize : ∀ w, 2 ≤ (S w).card)
    (gs : List Gate) (out : Fin m → ℕ)
    (hc : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true))
    (w : Fin m) : n ≤ out w ∧ out w < n + gs.length := by
  have hlow : n ≤ out w := by
    by_contra hn
    have holt : out w < n := by omega
    obtain ⟨v, hv, hne⟩ := (S w).exists_mem_ne (by have := hsize w; omega) ⟨out w, holt⟩
    have hneval : v.val ≠ out w := by
      intro he
      apply hne
      exact Fin.ext he
    have he := singleton_eval n m S gs out hc w v
    have hw := wires_input (⟨gs, out w⟩ : Circuit)
      (List.ofFn (fun z : Fin n => decide (z = v))) (out w) (by simpa using holt)
    simp only [Circuit.eval] at he
    rw [hw] at he
    have hg : (List.ofFn (fun z : Fin n => decide (z = v))).getD (out w) false = false := by
      simp [List.getD_eq_getElem?_getD, holt, Fin.ext_iff, Ne.symm hneval]
    rw [hg] at he
    simp [hv] at he
  refine ⟨hlow, ?_⟩
  by_contra hn
  have hbig : n + gs.length ≤ out w := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (S w).card by have := hsize w; omega)
  have he := singleton_eval n m S gs out hc w v
  simp only [Circuit.eval] at he
  rw [List.getD_eq_default _ _ (by rw [wires_length]; simpa using hbig)] at he
  simp [hv] at he

lemma output_count_bound (n m : ℕ) (S : Fin m → Finset (Fin n))
    (hsize : ∀ w, 2 ≤ (S w).card)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ)
    (hc : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    m ≤ gs.length := by
  let f : Fin m → Fin gs.length := fun w =>
    ⟨out w - n, by have := output_is_gate n m S hsize gs out hc w; omega⟩
  have hinj : Function.Injective f := by
    intro i j hij
    apply output_injective n m S hsize hinter gs out hc
    have he : out i - n = out j - n := congrArg Fin.val hij
    have hi := output_is_gate n m S hsize gs out hc i
    have hj := output_is_gate n m S hsize gs out hc j
    omega
  simpa using Fintype.card_le_of_injective f hinj

end PEqualNP.Outside.L_meta_951_aux

namespace PEqualNP.Outside.L_meta_951_aux
open PEqualNP.CircuitLowerBounds

lemma pairs_case : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, (S i).card = 2) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length := by
  intro n m S hsize hinter gs out _ _ hc
  have hb := output_count_bound n m S (fun w => by rw [hsize w]) hinter gs out hc
  simpa [hsize] using hb

end PEqualNP.Outside.L_meta_951_aux

#print axioms PEqualNP.Outside.L_meta_951_aux.pairs_case
