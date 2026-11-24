import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3756

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core

private lemma foldl_snoc_spec {α β : Type*} (step : List β → α → β)
    (init : List β) (gs : List α) :
    ∃ t : List β, gs.foldl (fun acc g => acc ++ [step acc g]) init = init ++ t ∧
      t.length = gs.length := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (init ++ [step init g])
    refine ⟨step init g :: t, ?_, by simp [hl]⟩
    simpa [List.foldl_cons, List.append_assoc] using ht

private lemma foldl_snoc_length {α β : Type*} (step : List β → α → β)
    (init : List β) (gs : List α) :
    (gs.foldl (fun acc g => acc ++ [step acc g]) init).length = init.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := foldl_snoc_spec step init gs
  rw [ht, List.length_append, hl]

private lemma foldl_snoc_getD_lt {α β : Type*} (step : List β → α → β)
    (init : List β) (gs : List α) (i : ℕ) (d : β) (hi : i < init.length) :
    (gs.foldl (fun acc g => acc ++ [step acc g]) init).getD i d = init.getD i d := by
  obtain ⟨t, ht, _⟩ := foldl_snoc_spec step init gs
  rw [ht, List.getD_append _ _ _ _ hi]

private lemma foldl_snoc_getD_at {α β : Type*} (step : List β → α → β)
    (init : List β) (gs : List α) (k : ℕ) (d : β) (hk : k < gs.length) :
    (gs.foldl (fun acc g => acc ++ [step acc g]) init).getD (init.length + k) d =
      step ((gs.take k).foldl (fun acc g => acc ++ [step acc g]) init) gs[k] := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := List.take_append_drop k gs
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1.symm
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  set pre := (gs.take k).foldl (fun acc g => acc ++ [step acc g]) init with hpre
  have hplen : pre.length = init.length + k := by
    rw [hpre, foldl_snoc_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [foldl_snoc_getD_lt step (pre ++ [step pre gs[k]]) (gs.drop (k + 1)) (init.length + k) d
    (by simp [hplen])]
  rw [← hplen]
  simp

private lemma foldl_snoc_getD_take {α β : Type*} (step : List β → α → β)
    (init : List β) (gs : List α) (k i : ℕ) (d : β) (hi : i < init.length + k) (hk : k ≤ gs.length) :
    ((gs.take k).foldl (fun acc g => acc ++ [step acc g]) init).getD i d =
      (gs.foldl (fun acc g => acc ++ [step acc g]) init).getD i d := by
  have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : ((gs.take k).foldl (fun acc g => acc ++ [step acc g]) init).length = init.length + k := by
    rw [foldl_snoc_length, List.length_take, Nat.min_eq_left hk]
  rw [foldl_snoc_getD_lt step _ (gs.drop k) i d (by omega)]

private lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  exact List.getD_eq_getElem C.gates _ hk

private lemma ao2_inputs {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) :
    ∃ a b : ℕ, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k ∧
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) := by
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq_getElem C k hk]
    exact List.getElem_mem hk
  have hlen : (gateAt C k).inputs.length = 2 := hAO2.2.2 _ hmem
  have hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := hAO2.1 _ hmem
  match hi : (gateAt C k).inputs with
  | [a, b] =>
    have ha : a < n + k := hAO2.2.1 k hk a (by rw [hi]; simp)
    have hb : b < n + k := hAO2.2.1 k hk b (by rw [hi]; simp)
    exact ⟨a, b, rfl, ha, hb, hop⟩
  | [] => simp [hi] at hlen
  | [_] => simp [hi] at hlen
  | _ :: _ :: _ :: _ => simp [hi] at hlen

private lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_snoc_length (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates

private lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  rw [foldl_snoc_getD_lt (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    (List.ofFn x) C.gates w false (by simp [hw])]
  rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_ofFn]

private lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {k : ℕ} (hk : k < C.gates.length) :
    wireVal n C (n + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => wireVal n C i x) := by
  unfold wireVal Circuit.wires
  have h1 := foldl_snoc_getD_at (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    (List.ofFn x) C.gates k false hk
  rw [List.length_ofFn] at h1
  rw [h1, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < n + k := hAO2.2.1 k hk i (by rw [gateAt_eq_getElem C k hk]; exact hi)
  exact foldl_snoc_getD_take (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    (List.ofFn x) C.gates k i false (by rw [List.length_ofFn]; exact hlt) (Nat.le_of_lt hk)

private lemma wireVal_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {k a b : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (hin : (gateAt C k).inputs = [a, b]) :
    wireVal n C (n + k) x = (wireVal n C a x && wireVal n C b x) := by
  rw [wireVal_gate hAO2 x hk, hop, hin]
  simp [GateOp.eval]

private lemma wireVal_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {k a b : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b]) :
    wireVal n C (n + k) x = (wireVal n C a x || wireVal n C b x) := by
  rw [wireVal_gate hAO2 x hk, hop, hin]
  simp [GateOp.eval]

private lemma cones_getD {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    (cones n C).getD k [] =
      ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  unfold cones
  have hstep : coneStep n = fun cs g => cs ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
  rw [hstep]
  have h0 : ([] : List (List ℕ)).length + k = k := by simp
  conv_lhs => rw [← h0]
  rw [foldl_snoc_getD_at _ [] C.gates k [] hk]
  rw [gateAt_eq_getElem C k hk]
  have hplen : ((C.gates.take k).foldl (fun acc g => acc ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) [])]) []).length = k := by
    rw [foldl_snoc_length, List.length_nil, zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [hplen]
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter] at hw
  have hwn : n ≤ w ∧ w < n + k := of_decide_eq_true hw.2
  congr 1
  exact foldl_snoc_getD_take _ [] C.gates k (w - n) [] (by omega) (Nat.le_of_lt hk)

private lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cones_getD hj, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hwn : n ≤ w ∧ w < n + j := of_decide_eq_true hw.2
    rw [List.mem_cons] at hi
    exact ⟨w, hw.1, hwn.1, hwn.2, hi⟩
  · rintro ⟨w, hw, h1, h2, hi⟩
    refine ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h1, h2⟩⟩, ?_⟩
    exact List.mem_cons.mpr hi

private lemma inCone_lt {n : ℕ} {C : Circuit} :
    ∀ j < C.gates.length, ∀ i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj i hij
    obtain ⟨w, _, h1, h2, h3 | h3⟩ := (inCone_iff hj).mp hij
    · omega
    · have := ih (w - n) (by omega) (by omega) i h3
      omega

private lemma inCone_trans {n : ℕ} {C : Circuit} :
    ∀ k < C.gates.length, ∀ i j, InCone n C i j → InCone n C j k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i j hij hjk
    obtain ⟨w, hw, h1, h2, rfl | h3⟩ := (inCone_iff hk).mp hjk
    · exact (inCone_iff hk).mpr ⟨w, hw, h1, h2, Or.inr hij⟩
    · have h4 : InCone n C i (w - n) := ih (w - n) (by omega) (by omega) i j hij h3
      exact (inCone_iff hk).mpr ⟨w, hw, h1, h2, Or.inr h4⟩

private lemma inOutputCone_step {n : ℕ} {C : Circuit} {j w : ℕ}
    (hj : InOutputCone n C j) (hw : w ∈ (gateAt C j).inputs) (h1 : n ≤ w) (h2 : w < n + j) :
    InOutputCone n C (w - n) := by
  have hjlen : j < C.gates.length := hj.1
  have hlt : w - n < j := by omega
  have hic : InCone n C (w - n) j := (inCone_iff hjlen).mpr ⟨w, hw, h1, h2, Or.inl rfl⟩
  refine ⟨by omega, ?_⟩
  rcases hj.2 with hout | ⟨hle, hco⟩
  · right
    refine ⟨by omega, ?_⟩
    have heq : C.output - n = j := by omega
    rw [heq]
    exact hic
  · right
    refine ⟨hle, ?_⟩
    have ho : C.output - n < C.gates.length := by
      by_contra hge
      have hlen : (cones n C).length = C.gates.length := by
        unfold cones
        have hstep : coneStep n = fun cs g => cs ++
            [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
        rw [hstep, foldl_snoc_length]
        simp
      have hnil : (cones n C).getD (C.output - n) [] = [] :=
        List.getD_eq_default _ _ (by omega)
      unfold InCone at hco
      rw [hnil] at hco
      simp at hco
    exact inCone_trans (C.output - n) ho (w - n) j hic hco

private lemma orStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    orStep n cs g = cs ++
      [cs.length :: match g.op with
        | GateOp.or =>
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => cs.getD (w - n) [])
        | _ => []] := by
  unfold orStep
  cases g.op <;> rfl

private lemma orSets_getD {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    (orSets n C).getD k [] =
      k :: match (gateAt C k).op with
        | GateOp.or =>
          ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
            (fun w => (orSets n C).getD (w - n) [])
        | _ => [] := by
  unfold orSets
  have hstep : orStep n = fun cs g => cs ++
      [cs.length :: match g.op with
        | GateOp.or =>
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => cs.getD (w - n) [])
        | _ => []] := funext fun cs => funext fun g => orStep_eq n cs g
  rw [hstep]
  have h1 := foldl_snoc_getD_at (fun cs g => cs.length :: match g.op with
        | GateOp.or =>
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => cs.getD (w - n) [])
        | _ => []) [] C.gates k [] hk
  rw [List.length_nil, zero_add] at h1
  rw [h1, gateAt_eq_getElem C k hk]
  have hplen : ((C.gates.take k).foldl (fun acc g => acc ++
      [acc.length :: match g.op with
        | GateOp.or =>
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => acc.getD (w - n) [])
        | _ => []]) []).length = k := by
    rw [foldl_snoc_length, List.length_nil, zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [hplen]
  congr 1
  cases C.gates[k].op <;> simp only []
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter] at hw
  have hwn : n ≤ w ∧ w < n + k := of_decide_eq_true hw.2
  exact foldl_snoc_getD_take _ [] C.gates k (w - n) [] (by omega) (Nat.le_of_lt hk)

private lemma orReaches_and_iff {n : ℕ} {C : Circuit} {k y : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) :
    OrReaches n C (n + k) y ↔ y = k := by
  unfold OrReaches
  have hsub : n + k - n = k := Nat.add_sub_cancel_left n k
  rw [hsub, orSets_getD hk, hop]
  simp

private lemma orReaches_or_iff {n : ℕ} {C : Circuit} {k a b y : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    OrReaches n C (n + k) y ↔ y = k ∨ OrReaches n C a y ∨ OrReaches n C b y := by
  unfold OrReaches
  have hsub : n + k - n = k := Nat.add_sub_cancel_left n k
  rw [hsub, orSets_getD hk, hop, hin]
  simp only [Nat.le_add_right, true_and, List.mem_cons, List.mem_flatMap, List.mem_filter]
  constructor
  · rintro (rfl | ⟨w, ⟨hwm, hwf⟩, hy⟩)
    · exact Or.inl rfl
    · have hwn : n ≤ w ∧ w < n + k := of_decide_eq_true hwf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
      rcases hwm with rfl | rfl
      · exact Or.inr (Or.inl ⟨hwn.1, hy⟩)
      · exact Or.inr (Or.inr ⟨hwn.1, hy⟩)
  · rintro (rfl | ⟨ha1, hy⟩ | ⟨hb1, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨a, ⟨by simp, decide_eq_true ⟨ha1, ha⟩⟩, hy⟩
    · exact Or.inr ⟨b, ⟨by simp, decide_eq_true ⟨hb1, hb⟩⟩, hy⟩

private lemma orReaches_le_and_cone {n : ℕ} {C : Circuit} :
    ∀ k < C.gates.length, ∀ y, OrReaches n C (n + k) y → y = k ∨ InCone n C y k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk y hreach
    unfold OrReaches at hreach
    rw [Nat.add_sub_cancel_left, orSets_getD hk, List.mem_cons] at hreach
    rcases hreach.2 with rfl | hmem
    · exact Or.inl rfl
    · cases hop : (gateAt C k).op with
      | or =>
        rw [hop] at hmem
        rw [List.mem_flatMap] at hmem
        obtain ⟨w, hw, hy⟩ := hmem
        rw [List.mem_filter] at hw
        have hwn : n ≤ w ∧ w < n + k := of_decide_eq_true hw.2
        have hreach' : OrReaches n C (n + (w - n)) y := by
          unfold OrReaches
          rw [Nat.add_sub_cancel_left]
          exact ⟨Nat.le_add_right _ _, hy⟩
        rcases ih (w - n) (by omega) (by omega) y hreach' with rfl | hic
        · exact Or.inr ((inCone_iff hk).mpr ⟨w, hw.1, hwn.1, hwn.2, Or.inl rfl⟩)
        · exact Or.inr ((inCone_iff hk).mpr ⟨w, hw.1, hwn.1, hwn.2, Or.inr hic⟩)
      | and => rw [hop] at hmem; simp at hmem
      | not => rw [hop] at hmem; simp at hmem
      | mod m => rw [hop] at hmem; simp at hmem
      | maj => rw [hop] at hmem; simp at hmem

private lemma orIn_input {n : ℕ} {C : Circuit} {w : ℕ} (hw : w < n) (t : Fin n) :
    t ∈ orIn n C w ↔ t.val = w := by
  unfold orIn OrReaches
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, _, ⟨hle, _⟩, _, _⟩)
    · exact h
    · omega
  · intro h
    exact Or.inl h

private lemma orIn_and {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (t : Fin n) :
    t ∉ orIn n C (n + k) := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rintro (ht | ⟨g, _, hreach, hgor, _⟩)
  · have := t.isLt; omega
  · have hgk : g = k := (orReaches_and_iff hk hop).mp hreach
    subst hgk
    rw [hop] at hgor
    cases hgor

private lemma orIn_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {k a b : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
    (hin : (gateAt C k).inputs = [a, b]) (t : Fin n) :
    t ∈ orIn n C (n + k) ↔ t ∈ orIn n C a ∨ t ∈ orIn n C b := by
  have ha : a < n + k := hAO2.2.1 k hk a (by rw [hin]; simp)
  have hb : b < n + k := hAO2.2.1 k hk b (by rw [hin]; simp)
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (ht | ⟨g, hgk, hreach, hgor, htin⟩)
    · have := t.isLt; omega
    · rcases (orReaches_or_iff hk hop hin ha hb).mp hreach with rfl | hra | hrb
      · rw [hin] at htin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htin
        rcases htin with hta | htb
        · exact Or.inl (Or.inl hta)
        · exact Or.inr (Or.inl htb)
      · exact Or.inl (Or.inr ⟨g, hgk, hra, hgor, htin⟩)
      · exact Or.inr (Or.inr ⟨g, hgk, hrb, hgor, htin⟩)
  · rintro ((hta | ⟨g, hgk, hra, hgor, htin⟩) | (htb | ⟨g, hgk, hrb, hgor, htin⟩))
    · exact Or.inr ⟨k, hk, (orReaches_or_iff hk hop hin ha hb).mpr (Or.inl rfl), hop,
        by rw [hin, hta]; simp⟩
    · exact Or.inr ⟨g, hgk, (orReaches_or_iff hk hop hin ha hb).mpr (Or.inr (Or.inl hra)), hgor, htin⟩
    · exact Or.inr ⟨k, hk, (orReaches_or_iff hk hop hin ha hb).mpr (Or.inl rfl), hop,
        by rw [hin, htb]; simp⟩
    · exact Or.inr ⟨g, hgk, (orReaches_or_iff hk hop hin ha hb).mpr (Or.inr (Or.inr hrb)), hgor, htin⟩

private lemma wireVal_oneHot_iff {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    (hOneHot : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t : Fin n, gateVal n C k (fun r => decide (r = t)) = false)
    (t : Fin n) :
    ∀ w < n + C.gates.length, wireVal n C w (fun r => decide (r = t)) = true ↔ t ∈ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wireVal_input n C _ w hlt, orIn_input hlt]
      simp only [decide_eq_true_eq]
      exact ⟨fun h => congrArg Fin.val h.symm, fun h => Fin.ext h.symm⟩
    · set k := w - n with hkdef
      have hw_eq : w = n + k := by omega
      have hk : k < C.gates.length := by omega
      rw [hw_eq]
      obtain ⟨a, b, hin, ha, hb, hop | hop⟩ := ao2_inputs hAO2 hk
      · have hval : wireVal n C (n + k) (fun r => decide (r = t)) = false := hOneHot k hk hop t
        rw [hval]
        exact ⟨fun h => Bool.noConfusion h, fun h => (orIn_and hk hop t h).elim⟩
      · rw [wireVal_or hAO2 _ hk hop hin, Bool.or_eq_true, orIn_or hAO2 hk hop hin,
          ih a (by omega) (by omega), ih b (by omega) (by omega)]

private lemma true_pair_reach {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) :
    ∀ w < n + C.gates.length, wireVal n C w (pairInput u v) = true →
      u ∈ orIn n C w ∨ v ∈ orIn n C w ∨
        ∃ Y < C.gates.length, OrReaches n C w Y ∧ (gateAt C Y).op = GateOp.and ∧
          gateVal n C Y (pairInput u v) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hval
    by_cases hlt : w < n
    · rw [wireVal_input n C _ w hlt] at hval
      unfold pairInput at hval
      simp only [decide_eq_true_eq] at hval
      rcases hval with h1 | h2
      · exact Or.inl ((orIn_input hlt u).mpr (congrArg Fin.val h1.symm))
      · exact Or.inr (Or.inl ((orIn_input hlt v).mpr (congrArg Fin.val h2.symm)))
    · set k := w - n with hkdef
      have hw_eq : w = n + k := by omega
      have hk : k < C.gates.length := by omega
      rw [hw_eq] at hval ⊢
      obtain ⟨a, b, hin, ha, hb, hop | hop⟩ := ao2_inputs hAO2 hk
      · exact Or.inr (Or.inr ⟨k, hk, (orReaches_and_iff hk hop).mpr rfl, hop, hval⟩)
      · rw [wireVal_or hAO2 _ hk hop hin, Bool.or_eq_true] at hval
        rcases hval with ha_val | hb_val
        · rcases ih a (by omega) (by omega) ha_val with hu | hv | ⟨Y, hY, hreach, hYop, hYval⟩
          · exact Or.inl ((orIn_or hAO2 hk hop hin u).mpr (Or.inl hu))
          · exact Or.inr (Or.inl ((orIn_or hAO2 hk hop hin v).mpr (Or.inl hv)))
          · exact Or.inr (Or.inr ⟨Y, hY,
              (orReaches_or_iff hk hop hin ha hb).mpr (Or.inr (Or.inl hreach)), hYop, hYval⟩)
        · rcases ih b (by omega) (by omega) hb_val with hu | hv | ⟨Y, hY, hreach, hYop, hYval⟩
          · exact Or.inl ((orIn_or hAO2 hk hop hin u).mpr (Or.inr hu))
          · exact Or.inr (Or.inl ((orIn_or hAO2 hk hop hin v).mpr (Or.inr hv)))
          · exact Or.inr (Or.inr ⟨Y, hY,
              (orReaches_or_iff hk hop hin ha hb).mpr (Or.inr (Or.inr hreach)), hYop, hYval⟩)

private lemma mem_foldl_insertNew {xs acc : List (List ℕ)} {v : List ℕ} :
    v ∈ xs.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    unfold insertNew
    split_ifs with h
    · constructor
      · rintro (ha | hxs)
        · exact Or.inl ha
        · exact Or.inr (Or.inr hxs)
      · rintro (ha | rfl | hxs)
        · exact Or.inl ha
        · exact Or.inl h
        · exact Or.inr hxs
    · simp only [List.mem_append, List.mem_singleton]
      tauto

private lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {v : List ℕ} :
    v ∈ andStep k A B ↔ ∃ p ∈ A, ∃ q ∈ B, v = capAdd k p q := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩

private lemma rv_input {n : ℕ} (C : Circuit) (u v : Fin n) (huv : u ≠ v) (w : ℕ) (hw : w < n) :
    (readVectors C n [u.val, v.val] 1).getD w [] =
      if w = u.val then [[1, 0]] else if w = v.val then [[0, 1]] else [] := by
  unfold readVectors
  rw [foldl_snoc_getD_lt _ _ C.gates w [] (by simp [hw])]
  rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_map, List.getElem_range]
  unfold leafVectors
  have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
  by_cases h1 : w = u.val
  · subst h1
    simp [hne, Ne.symm hne]
  · by_cases h2 : w = v.val
    · subst h2
      simp [h1, hne]
    · simp [h1, h2]

private lemma rv_gate_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (S : List ℕ)
    {k a b : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b]) (vec : List ℕ) :
    vec ∈ (readVectors C n S 1).getD (n + k) [] ↔
      vec ∈ (readVectors C n S 1).getD a [] ∨ vec ∈ (readVectors C n S 1).getD b [] := by
  let f : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    let ins := g.inputs.map fun i => R.getD i []
    match g.op with
    | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => ins.foldl (andStep 1) [S.map fun _ => 0]
    | _ => []
  have hrv : readVectors C n S 1 =
      C.gates.foldl (fun acc g => acc ++ [f acc g]) ((List.range n).map (leafVectors S 1)) := rfl
  rw [hrv]
  have h1 := foldl_snoc_getD_at f ((List.range n).map (leafVectors S 1)) C.gates k [] hk
  simp only [List.length_map, List.length_range] at h1
  rw [h1]
  have ha : a < n + k := hAO2.2.1 k hk a (by rw [hin]; simp)
  have hb : b < n + k := hAO2.2.1 k hk b (by rw [hin]; simp)
  have hta := foldl_snoc_getD_take f ((List.range n).map (leafVectors S 1)) C.gates k a []
    (by simp; omega) (Nat.le_of_lt hk)
  have htb := foldl_snoc_getD_take f ((List.range n).map (leafVectors S 1)) C.gates k b []
    (by simp; omega) (Nat.le_of_lt hk)
  simp only [f, ← gateAt_eq_getElem C k hk, hop, hin, List.map_cons, List.map_nil,
    List.foldl_cons, List.foldl_nil, hta, htb, mem_foldl_insertNew, List.not_mem_nil, false_or]

private lemma rv_gate_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (S : List ℕ)
    {k a b : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (hin : (gateAt C k).inputs = [a, b]) (vec : List ℕ) :
    vec ∈ (readVectors C n S 1).getD (n + k) [] ↔
      ∃ p ∈ (readVectors C n S 1).getD a [], ∃ q ∈ (readVectors C n S 1).getD b [],
        vec = capAdd 1 (capAdd 1 (S.map fun _ => 0) p) q := by
  let f : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    let ins := g.inputs.map fun i => R.getD i []
    match g.op with
    | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => ins.foldl (andStep 1) [S.map fun _ => 0]
    | _ => []
  have hrv : readVectors C n S 1 =
      C.gates.foldl (fun acc g => acc ++ [f acc g]) ((List.range n).map (leafVectors S 1)) := rfl
  rw [hrv]
  have h1 := foldl_snoc_getD_at f ((List.range n).map (leafVectors S 1)) C.gates k [] hk
  simp only [List.length_map, List.length_range] at h1
  rw [h1]
  have ha : a < n + k := hAO2.2.1 k hk a (by rw [hin]; simp)
  have hb : b < n + k := hAO2.2.1 k hk b (by rw [hin]; simp)
  have hta := foldl_snoc_getD_take f ((List.range n).map (leafVectors S 1)) C.gates k a []
    (by simp; omega) (Nat.le_of_lt hk)
  have htb := foldl_snoc_getD_take f ((List.range n).map (leafVectors S 1)) C.gates k b []
    (by simp; omega) (Nat.le_of_lt hk)
  simp only [f, ← gateAt_eq_getElem C k hk, hop, hin, List.map_cons, List.map_nil,
    List.foldl_cons, List.foldl_nil, hta, htb, mem_andStep]
  constructor
  · rintro ⟨r, ⟨z, hz, p, hp, rfl⟩, q, hq, rfl⟩
    simp only [List.mem_singleton] at hz
    subst hz
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨capAdd 1 (S.map fun _ => 0) p, ⟨S.map fun _ => 0, List.mem_singleton_self _, p, hp, rfl⟩,
      q, hq, rfl⟩

private lemma rv_shape {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v) :
    ∀ w < n + C.gates.length, ∀ vec ∈ (readVectors C n [u.val, v.val] 1).getD w [],
      ∃ c0 c1 : ℕ, vec = [c0, c1] ∧ c0 ≤ 2 ∧ c1 ≤ 2 ∧ 1 ≤ c0 + c1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw vec hvec
    by_cases hlt : w < n
    · rw [rv_input C u v huv w hlt] at hvec
      split_ifs at hvec
      · simp only [List.mem_singleton] at hvec
        exact ⟨1, 0, hvec, by omega, by omega, by omega⟩
      · simp only [List.mem_singleton] at hvec
        exact ⟨0, 1, hvec, by omega, by omega, by omega⟩
      · simp at hvec
    · set k := w - n with hkdef
      have hw_eq : w = n + k := by omega
      have hk : k < C.gates.length := by omega
      rw [hw_eq] at hvec
      obtain ⟨a, b, hin, ha, hb, hop | hop⟩ := ao2_inputs hAO2 hk
      · rw [rv_gate_and hAO2 [u.val, v.val] hk hop hin] at hvec
        obtain ⟨p, hp, q, hq, rfl⟩ := hvec
        obtain ⟨p0, p1, rfl, hp0, hp1, hpsum⟩ := ih a (by omega) (by omega) p hp
        obtain ⟨q0, q1, rfl, hq0, hq1, hqsum⟩ := ih b (by omega) (by omega) q hq
        refine ⟨min (min p0 2 + q0) 2, min (min p1 2 + q1) 2, ?_, Nat.min_le_right _ _,
          Nat.min_le_right _ _, by omega⟩
        simp [capAdd]
      · rw [rv_gate_or hAO2 [u.val, v.val] hk hop hin] at hvec
        rcases hvec with hp | hq
        · exact ih a (by omega) (by omega) vec hp
        · exact ih b (by omega) (by omega) vec hq

private lemma rv_and_pair {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v)
    {k a b : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (hin : (gateAt C k).inputs = [a, b])
    {p0 p1 q0 q1 : ℕ}
    (hp : [p0, p1] ∈ (readVectors C n [u.val, v.val] 1).getD a [])
    (hq : [q0, q1] ∈ (readVectors C n [u.val, v.val] 1).getD b []) :
    [min (p0 + q0) 2, min (p1 + q1) 2] ∈ (readVectors C n [u.val, v.val] 1).getD (n + k) [] := by
  have ha : a < n + k := hAO2.2.1 k hk a (by rw [hin]; simp)
  obtain ⟨r0, r1, hr, hr0, hr1, _⟩ := rv_shape hAO2 u v huv a (by omega) [p0, p1] hp
  simp only [List.cons.injEq, and_true] at hr
  rcases hr with ⟨rfl, rfl⟩
  rw [rv_gate_and hAO2 [u.val, v.val] hk hop hin]
  refine ⟨[p0, p1], hp, [q0, q1], hq, ?_⟩
  simp only [List.map_cons, List.map_nil, capAdd, List.zipWith_cons_cons, List.zipWith_nil,
    Nat.zero_add, Nat.min_eq_left hr0, Nat.min_eq_left hr1]

private lemma rv_unit_iff {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v) :
    ∀ w < n + C.gates.length,
      ([1, 0] ∈ (readVectors C n [u.val, v.val] 1).getD w [] ↔ u ∈ orIn n C w) ∧
      ([0, 1] ∈ (readVectors C n [u.val, v.val] 1).getD w [] ↔ v ∈ orIn n C w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [rv_input C u v huv w hlt, orIn_input hlt u, orIn_input hlt v]
      have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
      constructor
      · by_cases h1 : w = u.val
        · simp [h1]
        · by_cases h2 : w = v.val
          · subst h2
            simp [hne, Ne.symm hne]
          · simp [h1, h2, Ne.symm h1]
      · by_cases h1 : w = u.val
        · simp [h1, Ne.symm hne]
        · by_cases h2 : w = v.val
          · subst h2
            simp [Ne.symm hne]
          · simp [h1, h2, Ne.symm h2]
    · set k := w - n with hkdef
      have hw_eq : w = n + k := by omega
      have hk : k < C.gates.length := by omega
      rw [hw_eq]
      obtain ⟨a, b, hin, ha, hb, hop | hop⟩ := ao2_inputs hAO2 hk
      · constructor
        · refine ⟨?_, fun h => (orIn_and hk hop u h).elim⟩
          intro hmem
          rw [rv_gate_and hAO2 [u.val, v.val] hk hop hin] at hmem
          obtain ⟨p, hp, q, hq, heq⟩ := hmem
          obtain ⟨p0, p1, rfl, hp0, hp1, hpsum⟩ := rv_shape hAO2 u v huv a (by omega) p hp
          obtain ⟨q0, q1, rfl, hq0, hq1, hqsum⟩ := rv_shape hAO2 u v huv b (by omega) q hq
          simp only [List.map_cons, List.map_nil, capAdd, List.zipWith_cons_cons, List.zipWith_nil,
            Nat.zero_add, Nat.min_eq_left hp0, Nat.min_eq_left hp1, List.cons.injEq, and_true] at heq
          omega
        · refine ⟨?_, fun h => (orIn_and hk hop v h).elim⟩
          intro hmem
          rw [rv_gate_and hAO2 [u.val, v.val] hk hop hin] at hmem
          obtain ⟨p, hp, q, hq, heq⟩ := hmem
          obtain ⟨p0, p1, rfl, hp0, hp1, hpsum⟩ := rv_shape hAO2 u v huv a (by omega) p hp
          obtain ⟨q0, q1, rfl, hq0, hq1, hqsum⟩ := rv_shape hAO2 u v huv b (by omega) q hq
          simp only [List.map_cons, List.map_nil, capAdd, List.zipWith_cons_cons, List.zipWith_nil,
            Nat.zero_add, Nat.min_eq_left hp0, Nat.min_eq_left hp1, List.cons.injEq, and_true] at heq
          omega
      · rw [rv_gate_or hAO2 [u.val, v.val] hk hop hin, rv_gate_or hAO2 [u.val, v.val] hk hop hin,
          orIn_or hAO2 hk hop hin u, orIn_or hAO2 hk hop hin v]
        exact ⟨by rw [(ih a (by omega) (by omega)).1, (ih b (by omega) (by omega)).1],
          by rw [(ih a (by omega) (by omega)).2, (ih b (by omega) (by omega)).2]⟩

private def NoRead1 (n : ℕ) (C : Circuit) (u v : Fin n) (w : ℕ) : Prop :=
  ∀ vec ∈ (readVectors C n [u.val, v.val] 1).getD w [],
    ¬ (vec.all fun a => decide (a ≤ 1))

private lemma noRead1_of_and_no_unit {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    (u v : Fin n) (huv : u ≠ v) {k a b : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (hin : (gateAt C k).inputs = [a, b])
    (hside : (u ∉ orIn n C a ∧ v ∉ orIn n C a) ∨ (u ∉ orIn n C b ∧ v ∉ orIn n C b)) :
    NoRead1 n C u v (n + k) := by
  intro vec hvec hall
  have ha : a < n + k := hAO2.2.1 k hk a (by rw [hin]; simp)
  have hb : b < n + k := hAO2.2.1 k hk b (by rw [hin]; simp)
  rw [rv_gate_and hAO2 [u.val, v.val] hk hop hin] at hvec
  obtain ⟨p, hp, q, hq, rfl⟩ := hvec
  obtain ⟨p0, p1, rfl, hp0, hp1, hpsum⟩ := rv_shape hAO2 u v huv a (by omega) p hp
  obtain ⟨q0, q1, rfl, hq0, hq1, hqsum⟩ := rv_shape hAO2 u v huv b (by omega) q hq
  simp only [List.map_cons, List.map_nil, capAdd, List.zipWith_cons_cons, List.zipWith_nil,
    Nat.zero_add, Nat.min_eq_left hp0, Nat.min_eq_left hp1, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hall
  have hunitA := rv_unit_iff hAO2 u v huv a (by omega)
  have hunitB := rv_unit_iff hAO2 u v huv b (by omega)
  rcases hside with ⟨hna, hnb⟩ | ⟨hna, hnb⟩
  · have h10 : ¬ (p0 = 1 ∧ p1 = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hna (hunitA.1.mp hp)
    have h01 : ¬ (p0 = 0 ∧ p1 = 1) := by
      rintro ⟨rfl, rfl⟩
      exact hnb (hunitA.2.mp hp)
    omega
  · have h10 : ¬ (q0 = 1 ∧ q1 = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hna (hunitB.1.mp hq)
    have h01 : ¬ (q0 = 0 ∧ q1 = 1) := by
      rintro ⟨rfl, rfl⟩
      exact hnb (hunitB.2.mp hq)
    omega

private lemma descent {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    (hOneHot : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t : Fin n, gateVal n C k (fun r => decide (r = t)) = false)
    (u v : Fin n) (huv : u ≠ v) :
    ∀ j < C.gates.length, InOutputCone n C j →
      gateVal n C j (pairInput u v) = true → NoRead1 n C u v (n + j) →
      (∃ X < C.gates.length, ∃ Y < C.gates.length, ∃ (A Q P N : ℕ) (z w : Fin n),
        InOutputCone n C X ∧ (gateAt C X).op = GateOp.and ∧
        ((gateAt C X).inputs = [A, Q] ∨ (gateAt C X).inputs = [Q, A]) ∧
        (gateAt C Y).op = GateOp.and ∧
        ((gateAt C Y).inputs = [P, N] ∨ (gateAt C Y).inputs = [N, P]) ∧
        OrReaches n C Q Y ∧ ((z = u ∧ w = v) ∨ (z = v ∧ w = u)) ∧
        z ∈ orIn n C A ∧ z ∈ orIn n C P ∧ w ∈ orIn n C N) ∨
      (∃ W < C.gates.length, ∃ L M : ℕ,
        InOutputCone n C W ∧ (gateAt C W).op = GateOp.and ∧
        (gateAt C W).inputs = [L, M] ∧ gateVal n C W (pairInput u v) = true ∧
        u ∉ orIn n C L ∧ v ∉ orIn n C L ∧ u ∉ orIn n C M ∧ v ∉ orIn n C M) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hcone hval hno1
    obtain ⟨L, M, hin, hL, hM, hop | hop⟩ := ao2_inputs hAO2 hj
    · have hLM : wireVal n C L (pairInput u v) = true ∧ wireVal n C M (pairInput u v) = true := by
        have hv : wireVal n C (n + j) (pairInput u v) = true := hval
        rw [wireVal_and hAO2 _ hj hop hin, Bool.and_eq_true] at hv
        exact hv
      by_cases hall : u ∉ orIn n C L ∧ v ∉ orIn n C L ∧ u ∉ orIn n C M ∧ v ∉ orIn n C M
      · exact Or.inr ⟨j, hj, L, M, hcone, hop, hin, hval, hall.1, hall.2.1, hall.2.2.1, hall.2.2.2⟩
      · have hex : ∃ (A Q : ℕ) (z w : Fin n),
            ((gateAt C j).inputs = [A, Q] ∨ (gateAt C j).inputs = [Q, A]) ∧
            A < n + j ∧ Q < n + j ∧
            wireVal n C Q (pairInput u v) = true ∧
            ((z = u ∧ w = v) ∨ (z = v ∧ w = u)) ∧
            z ∈ orIn n C A := by
          by_cases huL : u ∈ orIn n C L
          · exact ⟨L, M, u, v, Or.inl hin, hL, hM, hLM.2, Or.inl ⟨rfl, rfl⟩, huL⟩
          by_cases hvL : v ∈ orIn n C L
          · exact ⟨L, M, v, u, Or.inl hin, hL, hM, hLM.2, Or.inr ⟨rfl, rfl⟩, hvL⟩
          by_cases huM : u ∈ orIn n C M
          · exact ⟨M, L, u, v, Or.inr hin, hM, hL, hLM.1, Or.inl ⟨rfl, rfl⟩, huM⟩
          by_cases hvM : v ∈ orIn n C M
          · exact ⟨M, L, v, u, Or.inr hin, hM, hL, hLM.1, Or.inr ⟨rfl, rfl⟩, hvM⟩
          exact (hall ⟨huL, hvL, huM, hvM⟩).elim
        obtain ⟨A, Q, z, w, hAQin, hA, hQ, hQval, hzw, hzA⟩ := hex
        have hzQ : z ∉ orIn n C Q := by
          intro hzQ
          have h1 := (wireVal_oneHot_iff hAO2 hOneHot z A (by omega)).mpr hzA
          have h2 := (wireVal_oneHot_iff hAO2 hOneHot z Q (by omega)).mpr hzQ
          have h3 : gateVal n C j (fun r => decide (r = z)) = true := by
            show wireVal n C (n + j) _ = true
            rcases hAQin with hAQ | hQA
            · rw [wireVal_and hAO2 _ hj hop hAQ, h1, h2]; rfl
            · rw [wireVal_and hAO2 _ hj hop hQA, h2, h1]; rfl
          have h4 := hOneHot j hj hop z
          rw [h3] at h4
          cases h4
        have hwQ : w ∉ orIn n C Q := by
          intro hwQ
          have h11 : [1, 1] ∈ (readVectors C n [u.val, v.val] 1).getD (n + j) [] := by
            rcases hzw with ⟨hzu, hwv⟩ | ⟨hzv, hwu⟩
            · rw [hzu] at hzA
              rw [hwv] at hwQ
              have hA10 : [1, 0] ∈ (readVectors C n [u.val, v.val] 1).getD A [] :=
                (rv_unit_iff hAO2 u v huv A (by omega)).1.mpr hzA
              have hQ01 : [0, 1] ∈ (readVectors C n [u.val, v.val] 1).getD Q [] :=
                (rv_unit_iff hAO2 u v huv Q (by omega)).2.mpr hwQ
              rcases hAQin with hAQ | hQA
              · exact rv_and_pair hAO2 u v huv hj hop hAQ hA10 hQ01
              · exact rv_and_pair hAO2 u v huv hj hop hQA hQ01 hA10
            · rw [hzv] at hzA
              rw [hwu] at hwQ
              have hA01 : [0, 1] ∈ (readVectors C n [u.val, v.val] 1).getD A [] :=
                (rv_unit_iff hAO2 u v huv A (by omega)).2.mpr hzA
              have hQ10 : [1, 0] ∈ (readVectors C n [u.val, v.val] 1).getD Q [] :=
                (rv_unit_iff hAO2 u v huv Q (by omega)).1.mpr hwQ
              rcases hAQin with hAQ | hQA
              · exact rv_and_pair hAO2 u v huv hj hop hAQ hA01 hQ10
              · exact rv_and_pair hAO2 u v huv hj hop hQA hQ10 hA01
          exact hno1 [1, 1] h11 (by decide)
        have huvQ : u ∉ orIn n C Q ∧ v ∉ orIn n C Q := by
          rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hzQ, hwQ⟩
          · exact ⟨hwQ, hzQ⟩
        rcases true_pair_reach hAO2 u v Q (by omega) hQval with huQ | hvQ | ⟨Y, hY, hreach, hYop, hYval⟩
        · exact (huvQ.1 huQ).elim
        · exact (huvQ.2 hvQ).elim
        · obtain ⟨P', N', hYin, hP', hN', _⟩ := ao2_inputs hAO2 hY
          by_cases hpat1 : (z ∈ orIn n C P' ∧ w ∈ orIn n C N') ∨ (z ∈ orIn n C N' ∧ w ∈ orIn n C P')
          · rcases hpat1 with ⟨hzP, hwN⟩ | ⟨hzN, hwP⟩
            · exact Or.inl ⟨j, hj, Y, hY, A, Q, P', N', z, w, hcone, hop, hAQin, hYop,
                Or.inl hYin, hreach, hzw, hzA, hzP, hwN⟩
            · exact Or.inl ⟨j, hj, Y, hY, A, Q, N', P', z, w, hcone, hop, hAQin, hYop,
                Or.inr hYin, hreach, hzw, hzA, hzN, hwP⟩
          · have hnoSame : ∀ t : Fin n, ¬ (t ∈ orIn n C P' ∧ t ∈ orIn n C N') := by
              intro t ⟨ht1, ht2⟩
              have h1 := (wireVal_oneHot_iff hAO2 hOneHot t P' (by omega)).mpr ht1
              have h2 := (wireVal_oneHot_iff hAO2 hOneHot t N' (by omega)).mpr ht2
              have h3 : gateVal n C Y (fun r => decide (r = t)) = true := by
                show wireVal n C (n + Y) _ = true
                rw [wireVal_and hAO2 _ hY hYop hYin, h1, h2]
                rfl
              have h4 := hOneHot Y hY hYop t
              rw [h3] at h4
              cases h4
            have hside : (u ∉ orIn n C P' ∧ v ∉ orIn n C P') ∨
                (u ∉ orIn n C N' ∧ v ∉ orIn n C N') := by
              by_cases hzP : z ∈ orIn n C P'
              · have hzN : z ∉ orIn n C N' := fun h => hnoSame z ⟨hzP, h⟩
                have hwN : w ∉ orIn n C N' := fun h => hpat1 (Or.inl ⟨hzP, h⟩)
                rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inr ⟨hzN, hwN⟩
                · exact Or.inr ⟨hwN, hzN⟩
              · by_cases hwP : w ∈ orIn n C P'
                · have hwN : w ∉ orIn n C N' := fun h => hnoSame w ⟨hwP, h⟩
                  have hzN : z ∉ orIn n C N' := fun h => hpat1 (Or.inr ⟨h, hwP⟩)
                  rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Or.inr ⟨hzN, hwN⟩
                  · exact Or.inr ⟨hwN, hzN⟩
                · rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Or.inl ⟨hzP, hwP⟩
                  · exact Or.inl ⟨hwP, hzP⟩
            have hYno1 : NoRead1 n C u v (n + Y) :=
              noRead1_of_and_no_unit hAO2 u v huv hY hYop hYin hside
            have hQge : n ≤ Q := hreach.1
            have hQmem : Q ∈ (gateAt C j).inputs := by
              rcases hAQin with hAQ | hQA
              · rw [hAQ]; simp
              · rw [hQA]; simp
            have hQcone : InOutputCone n C (Q - n) := inOutputCone_step hcone hQmem hQge hQ
            have hQreach : OrReaches n C (n + (Q - n)) Y := by
              have : n + (Q - n) = Q := Nat.add_sub_of_le hQge
              rwa [this]
            have hYlt : Y < j ∧ InOutputCone n C Y := by
              rcases orReaches_le_and_cone (Q - n) (by omega) Y hQreach with rfl | hYic
              · exact ⟨by omega, hQcone⟩
              · have hYl : Y < Q - n := inCone_lt (Q - n) (by omega) Y hYic
                refine ⟨by omega, hY, ?_⟩
                rcases hQcone.2 with hout | ⟨hle, hco⟩
                · right
                  refine ⟨by omega, ?_⟩
                  have heq : C.output - n = Q - n := by omega
                  rw [heq]
                  exact hYic
                · right
                  have ho : C.output - n < C.gates.length := by
                    by_contra hge
                    have hlen : (cones n C).length = C.gates.length := by
                      unfold cones
                      have hstep : coneStep n = fun cs g => cs ++
                          [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
                            (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
                      rw [hstep, foldl_snoc_length]
                      simp
                    have hnil : (cones n C).getD (C.output - n) [] = [] :=
                      List.getD_eq_default _ _ (by omega)
                    unfold InCone at hco
                    rw [hnil] at hco
                    simp at hco
                  exact ⟨hle, inCone_trans (C.output - n) ho Y (Q - n) hYic hco⟩
            exact ih Y hYlt.1 hY hYlt.2 hYval hYno1
    · have hv : wireVal n C (n + j) (pairInput u v) = true := hval
      rw [wireVal_or hAO2 _ hj hop hin, Bool.or_eq_true] at hv
      have hstep_or : ∀ c : ℕ, c ∈ (gateAt C j).inputs → c < n + j →
          wireVal n C c (pairInput u v) = true →
          (∀ vec ∈ (readVectors C n [u.val, v.val] 1).getD c [],
            vec ∈ (readVectors C n [u.val, v.val] 1).getD (n + j) []) →
          (∃ X < C.gates.length, ∃ Y < C.gates.length, ∃ (A Q P N : ℕ) (z w : Fin n),
            InOutputCone n C X ∧ (gateAt C X).op = GateOp.and ∧
            ((gateAt C X).inputs = [A, Q] ∨ (gateAt C X).inputs = [Q, A]) ∧
            (gateAt C Y).op = GateOp.and ∧
            ((gateAt C Y).inputs = [P, N] ∨ (gateAt C Y).inputs = [N, P]) ∧
            OrReaches n C Q Y ∧ ((z = u ∧ w = v) ∨ (z = v ∧ w = u)) ∧
            z ∈ orIn n C A ∧ z ∈ orIn n C P ∧ w ∈ orIn n C N) ∨
          (∃ W < C.gates.length, ∃ L M : ℕ,
            InOutputCone n C W ∧ (gateAt C W).op = GateOp.and ∧
            (gateAt C W).inputs = [L, M] ∧ gateVal n C W (pairInput u v) = true ∧
            u ∉ orIn n C L ∧ v ∉ orIn n C L ∧ u ∉ orIn n C M ∧ v ∉ orIn n C M) := by
        intro c hcmem hclt hcval hcsub
        have hcno1 : NoRead1 n C u v c := fun vec hvec => hno1 vec (hcsub vec hvec)
        by_cases hcn : c < n
        · exfalso
          rw [wireVal_input n C _ c hcn] at hcval
          unfold pairInput at hcval
          simp only [decide_eq_true_eq] at hcval
          rcases hcval with hcu | hcv
          · have hcu' : c = u.val := congrArg Fin.val hcu
            have h10 : [1, 0] ∈ (readVectors C n [u.val, v.val] 1).getD c [] := by
              rw [rv_input C u v huv c hcn]
              simp [hcu']
            exact hcno1 [1, 0] h10 (by decide)
          · have hcv' : c = v.val := congrArg Fin.val hcv
            have h01 : [0, 1] ∈ (readVectors C n [u.val, v.val] 1).getD c [] := by
              rw [rv_input C u v huv c hcn]
              have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
              simp [hcv', Ne.symm hne]
            exact hcno1 [0, 1] h01 (by decide)
        · have hcge : n ≤ c := by omega
          have hccone : InOutputCone n C (c - n) := inOutputCone_step hcone hcmem hcge hclt
          have hceq : n + (c - n) = c := Nat.add_sub_of_le hcge
          exact ih (c - n) (by omega) (by omega) hccone (by show wireVal n C (n + (c - n)) _ = true; rwa [hceq])
            (by rwa [hceq])
      rcases hv with hLv | hMv
      · exact hstep_or L (by rw [hin]; simp) hL hLv
          (fun vec hvec => (rv_gate_or hAO2 [u.val, v.val] hj hop hin vec).mpr (Or.inl hvec))
      · exact hstep_or M (by rw [hin]; simp) hM hMv
          (fun vec hvec => (rv_gate_or hAO2 [u.val, v.val] hj hop hin vec).mpr (Or.inr hvec))

end PEqualNP.Outside.L_meta_3756

theorem PEqualNP.Outside.L_meta_3756 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (fun r => decide (r = t)) = false) → ∀ (u v : Fin n) (o : ℕ), G.Adj u v → C.output = n + o → PEqualNP.Core.ReadTwiceAt n C o u v → (∃ X < C.gates.length, ∃ Y < C.gates.length, ∃ (A Q P N : ℕ) (z w : Fin n), PEqualNP.Core.InOutputCone n C X ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C X).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C X).inputs = [A, Q] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C X).inputs = [Q, A]) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C Y).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C Y).inputs = [P, N] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C Y).inputs = [N, P]) ∧ PEqualNP.CleanedNonEdge.OrReaches n C Q Y ∧ ((z = u ∧ w = v) ∨ (z = v ∧ w = u)) ∧ z ∈ PEqualNP.TopForm.orIn n C A ∧ z ∈ PEqualNP.TopForm.orIn n C P ∧ w ∈ PEqualNP.TopForm.orIn n C N) ∨ (∃ W < C.gates.length, ∃ L M : ℕ, PEqualNP.Core.InOutputCone n C W ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C W).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C W).inputs = [L, M] ∧ PEqualNP.EdgeOwnership.gateVal n C W (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ u ∉ PEqualNP.TopForm.orIn n C L ∧ v ∉ PEqualNP.TopForm.orIn n C L ∧ u ∉ PEqualNP.TopForm.orIn n C M ∧ v ∉ PEqualNP.TopForm.orIn n C M) := by
  intro n G _ C hAO2 hFun hOneHot u v o hAdj hOut hRT
  have huv : u ≠ v := hAdj.ne
  have hEval : PEqualNP.EdgeOwnership.gateVal n C o (PEqualNP.EdgeOwnership.pairInput u v) = true := by
    have h1 : PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput u v) :=
      congrFun hFun _
    have h2 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput u v) = true := by
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun PEqualNP.EdgeOwnership.pairInput
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨u, v, hAdj, Or.inl rfl, Or.inr rfl⟩
    have h3 : PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) =
        PEqualNP.EdgeOwnership.gateVal n C o (PEqualNP.EdgeOwnership.pairInput u v) := by
      unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
        PEqualNP.EdgeOwnership.gateVal
      rw [hOut]
    rw [← h3, h1, h2]
  have ho : o < C.gates.length := by
    by_contra hge
    have hlen : (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).length = n + C.gates.length := by
      rw [PEqualNP.Outside.L_meta_3756.wires_length]
      simp
    have hdef : PEqualNP.EdgeOwnership.gateVal n C o (PEqualNP.EdgeOwnership.pairInput u v) = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hEval] at hdef
    cases hdef
  have hcone : PEqualNP.Core.InOutputCone n C o := ⟨ho, Or.inl hOut⟩
  have hno1 : PEqualNP.Outside.L_meta_3756.NoRead1 n C u v (n + o) := by
    intro vec hvec hall
    unfold PEqualNP.Core.ReadTwiceAt PEqualNP.ReadK.readsAtMost PEqualNP.Core.atGate at hRT
    have htrue : ((PEqualNP.ReadK.readVectors C n [u.val, v.val] 1).getD (n + o) []).any
        (fun x => x.all fun a => decide (a ≤ 1)) = true :=
      List.any_eq_true.mpr ⟨vec, hvec, hall⟩
    change ((PEqualNP.ReadK.readVectors C n [u.val, v.val] 1).getD (n + o) []).any
        (fun x => x.all fun a => decide (a ≤ 1)) = false at hRT
    rw [htrue] at hRT
    cases hRT
  exact PEqualNP.Outside.L_meta_3756.descent hAO2 hOneHot u v huv o ho hcone hEval hno1
