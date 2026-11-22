import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0006
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.JpqMulMonomialEqMulSignDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MonomialSign

theorem diagonal_mul_eq {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι) (ε : ι → ℝ) (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (M : Matrix ι κ ℂ) (d : κ → ℝ) (hd : ∀ i, d i ≠ 0)
    (hM : Mᴴ * Matrix.diagonal (fun a => (ε a : ℂ)) * M = Matrix.diagonal (fun i => (d i : ℂ)))
    (hrow : ∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) :
    Matrix.diagonal (fun a => (ε a : ℂ)) * M
      = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  have hsum : ∀ i, d i = ∑ a, ε a * Complex.normSq (M a i) := by
    intro i
    have h := congrFun (congrFun hM i) i
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply] at h
    apply Complex.ofReal_injective
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self,
      Complex.star_def]
    ring
  have hex : ∀ i, ∃ a, M a i ≠ 0 := by
    intro i
    by_contra hne
    push Not at hne
    apply hd i
    rw [hsum i]
    simp [hne]
  choose r hr using hex
  have hinj : Function.Injective r := fun i j hij => hrow (r i) i j (hr i) (hij ▸ hr j)
  have hbij : Function.Bijective r :=
    (Fintype.bijective_iff_injective_and_card r).2 ⟨hinj, hcard⟩
  have huniq : ∀ a i, M a i ≠ 0 → a = r i := by
    intro a i h
    obtain ⟨j, rfl⟩ := hbij.2 a
    rw [hrow (r j) i j h (hr j)]
  ext a i
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : M a i = 0
  · simp [h]
  · have ha := huniq a i h
    have hdi : d i = ε a * Complex.normSq (M a i) := by
      rw [hsum i]
      refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
      have : M b i = 0 := by
        by_contra hb'
        exact hb ((huniq b i hb').trans ha.symm)
      simp [this]
    have hpos : 0 < Complex.normSq (M a i) := Complex.normSq_pos.2 h
    rcases hε a with h1 | h1
    · have : 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]
    · have : ¬ 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]

theorem Jpq_mul_eq : ∀ (n p q : ℕ), p + q = n → ∀ (M : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) → Mᴴ * Formalism.UG.Jpq p q * M = Matrix.diagonal (fun i => (d i : ℂ)) → (∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) → Formalism.UG.Jpq p q * M = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  intro n p q hn M d hd hM hrow
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal
      (fun a => ((Sum.elim (fun _ => 1) (fun _ => -1) a : ℝ) : ℂ)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ] at hM ⊢
  refine diagonal_mul_eq (by simp [hn]) _ ?_ M d hd hM hrow
  rintro (a | a) <;> simp

end GlobalTheory.MonomialSign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemOfIsKilledByOperatorProductsVacuumCreation
section
noncomputable section

namespace GlobalTheory.FockCompare.WeylInduct

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M]

theorem killed_zero (a : I → Module.End ℂ M) (m : M) : Killed a 0 m ↔ m = 0 := by
  constructor
  · intro h; exact h [] rfl
  · intro h l hl
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact h

theorem killed_succ (a : I → Module.End ℂ M) (N : ℕ) (m : M) :
    Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    obtain rfl | ⟨l', i, rfl⟩ := List.eq_nil_or_concat l
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

noncomputable def prodE (E : Module.End ℂ M) (lam : ℂ) : ℕ → ℕ → M → M
  | 0, _, x => x
  | N + 1, j, x => prodE E lam N (j + 1) (E x - ((j : ℂ) * lam) • x)

theorem prodE_comm (E : Module.End ℂ M) (lam : ℂ) (N : ℕ) :
    ∀ (j : ℕ) (x : M), prodE E lam N j (E x) = E (prodE E lam N j x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [← ih, map_sub, map_smul]

theorem shift_prodE (E A : Module.End ℂ M) (lam : ℂ) (h : ∀ x, A (E x) = E (A x) + lam • A x) (N : ℕ) :
    ∀ (j : ℕ) (x : M), A (prodE E lam N (j + 1) x) = prodE E lam N j (A x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [ih, map_sub, map_smul, h]
    congr 1
    push_cast
    module

theorem killed_stable (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (N : ℕ) :
    ∀ (t : ℂ) (x : M), Killed a N x → Killed a N (E x - t • x) := by
  induction N with
  | zero => intro t x hx; rw [killed_zero] at hx ⊢; simp [hx]
  | succ N ih =>
    intro t x hx
    rw [killed_succ] at hx ⊢
    intro i
    have e : a i (E x - t • x) = E (a i x) - (t - lam) • a i x := by
      rw [map_sub, map_smul, h]; module
    rw [e]
    exact ih _ _ (hx i)

theorem prodE_kills (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (h0 : ∀ x, (∀ i, a i x = 0) → E x = 0) (N : ℕ) :
    ∀ x : M, Killed a N x → prodE E lam N 0 x = 0 := by
  induction N with
  | zero => intro x hx; exact (killed_zero a x).1 hx
  | succ N ih =>
    intro x hx
    rw [killed_succ] at hx
    simp only [prodE, Nat.cast_zero, zero_mul, zero_smul, sub_zero]
    rw [prodE_comm]
    refine h0 _ fun i => ?_
    rw [shift_prodE E (a i) lam (h i), ih _ (hx i)]

theorem peel (E : Module.End ℂ M) (lam : ℂ) (hl : lam ≠ 0) (S : M → Prop) (P : Submodule ℂ M)
    (hS : ∀ (t : ℂ) x, S x → S (E x - t • x)) (hE : ∀ x, S x → E x ∈ P) (K : ℕ) :
    ∀ (j : ℕ) (x : M), S x → prodE E lam K (j + 1) x ∈ P → x ∈ P := by
  induction K with
  | zero => intro j x _ hx; exact hx
  | succ K ih =>
    intro j x hx hp
    simp only [prodE] at hp
    have h1 := ih _ _ (hS _ x hx) hp
    have h2 := P.sub_mem (hE x hx) h1
    rw [sub_sub_cancel] at h2
    exact (P.smul_mem_iff (mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)) hl)).1 h2

theorem mem_of_killed : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a c : I → Module.End ℂ M) (n : ℕ) (e : Fin n → I) (lam : ℂ), lam ≠ 0 → (∀ i, a i * (∑ k, c (e k) * a (e k)) = ((∑ k, c (e k) * a (e k)) + lam • (1 : Module.End ℂ M)) * a i) → ∀ P : Submodule ℂ M, (∀ m, (∀ i, a i m = 0) → m ∈ P) → (∀ i, ∀ m ∈ P, c i m ∈ P) → ∀ (N : ℕ) (m : M), Killed a N m → m ∈ P := by
  intro I M _ _ a c n e lam hl hc P hv hP N
  set E : Module.End ℂ M := ∑ k, c (e k) * a (e k) with hEdef
  have hEx : ∀ x, E x = ∑ k, c (e k) (a (e k) x) := by
    intro x; simp [hEdef, LinearMap.sum_apply]
  have h : ∀ i x, a i (E x) = E (a i x) + lam • a i x := by
    intro i x
    have := LinearMap.congr_fun (hc i) x
    simpa using this
  have h0 : ∀ x, (∀ i, a i x = 0) → E x = 0 := by
    intro x hx; simp [hEx, hx]
  induction N with
  | zero => intro m hm; rw [(killed_zero a m).1 hm]; exact P.zero_mem
  | succ N ih =>
    intro m hm
    refine peel E lam hl (Killed a (N + 1)) P (killed_stable a E lam h (N + 1)) (fun x hx => ?_) N 0 m hm
      (hv _ fun i => ?_)
    · rw [hEx]
      exact P.sum_mem fun k _ => hP _ _ (ih _ ((killed_succ a N x).1 hx _))
    · rw [shift_prodE E (a i) lam (h i)]
      exact prodE_kills a E lam h h0 N _ ((killed_succ a N m).1 hm i)

end GlobalTheory.FockCompare.WeylInduct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MyTiedNotMeasTupleTied
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedMeasureTuples Formalism.UG.P

namespace GlobalTheory.MeasTupleEq

theorem indexValue_eq_parIdx (q : ℝ) (r d : ℕ) : indexValue q r d = parIdx q r d := by
  simp only [indexValue, parIdx, zpow_neg, zpow_natCast]

theorem map_residue_surjective (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  classical
  let M : Matrix (Fin n) (Fin n) O := fun a b =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) ((g : Matrix (Fin n) (Fin n) _) a b)
  have hM : M.map (IsLocalRing.residue O) = (g : Matrix (Fin n) (Fin n) _) := by
    ext a b
    simp only [M]
    exact Function.surjInv_eq _ _
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (IsLocalRing.residue O M.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det g).isUnit
    exact (isUnit_map_iff (IsLocalRing.residue O) _).1 h1
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hdet, Units.ext ?_⟩
  exact hM

theorem index_parahoric (O : Type) [CommRing O] [IsLocalRing O] (r d : ℕ) :
    (parahoric (IsLocalRing.maximalIdeal O) r d).index =
      (parahoric (⊥ : Ideal (IsLocalRing.ResidueField O)) r d).index := by
  rw [← Subgroup.index_comap_of_surjective _ (map_residue_surjective O (r + d))]
  congr 1
  ext h
  rw [Subgroup.mem_comap]
  refine forall_congr' fun i => forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [Ideal.mem_bot]
  exact (IsLocalRing.residue_eq_zero_iff _).symm

def glT {k : Type} [Field k] {n : ℕ} (g : GL (Fin n) k) : GL (Fin n) k :=
  ⟨(g : Matrix (Fin n) (Fin n) k).transpose, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem index_upper_eq_lower (k : Type) [Field k] [Fintype k] (r d : ℕ) :
    (parahoric (⊥ : Ideal k) r d).index = (tjcosets_par (𝔽 := k) (r + d) r).index := by
  classical
  have hc : Nat.card (parahoric (⊥ : Ideal k) r d) = Nat.card (tjcosets_par (𝔽 := k) (r + d) r) :=
    Nat.card_congr
      { toFun := fun g => ⟨glT g.1, fun a b ha hb => Ideal.mem_bot.1 (g.2 b a hb ha)⟩
        invFun := fun g => ⟨glT g.1, fun a b ha hb => Ideal.mem_bot.2 (g.2 b a hb ha)⟩
        left_inv := fun g => Subtype.ext (Units.ext rfl)
        right_inv := fun g => Subtype.ext (Units.ext rfl) }
  have h1 := (parahoric (⊥ : Ideal k) r d).index_mul_card
  have h2 := (tjcosets_par (𝔽 := k) (r + d) r).index_mul_card
  rw [hc, ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

theorem prod_one_sub {q : ℝ} (hq : q ≠ 0) (n : ℕ) :
    (∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)) * q ^ (∑ i ∈ Finset.range n, (i + 1)) =
      ∏ i ∈ Finset.range n, (q ^ (i + 1) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Finset.sum_range_succ, Finset.prod_range_succ, ← ih,
      pow_add q (∑ i ∈ Finset.range n, (i + 1))]
    have : (1 - (q ^ (n + 1))⁻¹) * q ^ (n + 1) = q ^ (n + 1) - 1 := by field_simp
    rw [← this]; ring

theorem sum_add (r d : ℕ) : ∑ i ∈ Finset.range (r + d), (i + 1) =
    r * d + (∑ i ∈ Finset.range r, (i + 1) + ∑ i ∈ Finset.range d, (i + 1)) := by
  induction d with
  | zero => simp
  | succ d ih => rw [← add_assoc, Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring

theorem eq_indexValue {q : ℝ} (hq : 1 < q) (r d : ℕ) (C : ℝ)
    (h : C * (∏ i ∈ Finset.range r, (q ^ (i + 1) - 1)) * ∏ i ∈ Finset.range d, (q ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range (r + d), (q ^ (i + 1) - 1)) : C = indexValue q r d := by
  have h0 : q ≠ 0 := by linarith
  have hp : ∀ n, (∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)) ≠ 0 := fun n => by
    have := (GlobalTheory.MeasTuple.prod_pos' hq n).ne'
    simpa only [zpow_neg, zpow_natCast] using this
  rw [← prod_one_sub h0, ← prod_one_sub h0, ← prod_one_sub h0, sum_add, pow_add, pow_add] at h
  unfold indexValue
  rw [eq_div_iff (mul_ne_zero (hp r) (hp d))]
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero (∑ i ∈ Finset.range r, (i + 1)) h0)
    (pow_ne_zero (∑ i ∈ Finset.range d, (i + 1)) h0))
  linear_combination h

theorem index_field (k : Type) [Field k] [Fintype k] (r d : ℕ) :
    ((parahoric (⊥ : Ideal k) r d).index : ℝ) = indexValue (Fintype.card k : ℝ) r d := by
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have h := tjcosets_arith _ (r + d) r _ hq (by omega) (tjcosets_ff_count (𝔽 := k) (r + d) r (by omega))
  have h2 := tjcosets_prod_shift (Fintype.card k : ℤ) d r
  rw [add_comm d r, ← h, ← index_upper_eq_lower, mul_comm] at h2
  apply eq_indexValue (by exact_mod_cast hq)
  exact_mod_cast h2

theorem indexFormula : IndexFormula := by
  intro F _ _ v r d
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := tjcosets_finite v
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  have hc := tjcosets_card_residue v
  rw [Nat.card_eq_fintype_card] at hc
  unfold localIndex
  rw [index_parahoric, index_field, hc]
  rfl

theorem localIndex_ne_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {r d : ℕ} (hr : 0 < r)
    (hd : 0 < d) : localIndex v r d ≠ 1 := by
  intro h
  unfold localIndex at h
  rw [Subgroup.index_eq_one, eq_top_iff] at h
  let i : Fin (r + d) := ⟨r, by omega⟩
  let k : Fin (r + d) := ⟨0, by omega⟩
  have hik : i ≠ k := fun e => by have := congrArg Fin.val e; simp only [i, k] at this; omega
  have hdet : IsUnit (Matrix.transvection i k (1 : v.adicCompletionIntegers F)).det := by
    rw [Matrix.det_transvection_of_ne i k hik]; exact isUnit_one
  have hm := h (Subgroup.mem_top (Matrix.GeneralLinearGroup.mk'' _ hdet)) i k le_rfl hr
  have he : (Matrix.transvection i k (1 : v.adicCompletionIntegers F)) i k = 1 := by
    simp [Matrix.transvection, Matrix.one_apply_ne hik]
  have hm' : (1 : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal _ := he ▸ hm
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hm')

variable {D : D7} {X : ThetaX D}

theorem myTied_iff_abstract (X : ThetaX D) (Z : DivX D) : ThetaDivisorCompatibility X Z ↔ MeasFactorAbstract X Z := by
  unfold ThetaDivisorCompatibility ThetaX.TieMY MeasFactorAbstract
  simp only [indexValue_eq_parIdx]

theorem prod_localIndex {T : ThetaTied D X} {Z : DivX D} {μ : D.what₂.Tup} (e : Z.QPl μ ≃ ramPlaces T μ)
    (he : ∀ x, Z.qv μ x = Ideal.absNorm (e x).1.asIdeal) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : (↑S : Set _) = ramPlaces T μ) (r d : ℕ) :
    ∏ v ∈ S, (localIndex v r d : ℝ) = ∏ x : Z.QPl μ, parIdx (Z.qv μ x) r d := by
  symm
  refine Finset.prod_bij (fun x _ => (e x).1) (fun x _ => ?_) (fun x _ y _ hxy => ?_) (fun v hv => ?_) (fun x _ => ?_)
  · exact Finset.mem_coe.mp (hS.symm.subset (e x).2)
  · exact e.injective (Subtype.ext hxy)
  · have hv' : v ∈ ramPlaces T μ := by rw [← hS]; exact hv
    exact ⟨e.symm ⟨v, hv'⟩, Finset.mem_univ _, by simp⟩
  · rw [he x, indexFormula, indexValue_eq_parIdx]

theorem factor_iff_myTied {T : ThetaTied D X} {Z : DivX D} (hP : PlacesTied T Z) : MeasFactor T ↔ ThetaDivisorCompatibility X Z := by
  refine forall_congr' fun μ => ?_
  obtain ⟨e, he⟩ := hP μ
  constructor
  · rintro ⟨S, hS, hm⟩ j hj
    rw [hm j hj, prod_localIndex e he S hS]
  · intro h
    have hfin : (ramPlaces T μ).Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e)
    refine ⟨hfin.toFinset, hfin.coe_toFinset, fun j hj => ?_⟩
    rw [h j hj, prod_localIndex e he _ hfin.coe_toFinset]

theorem measTupleTied_iff (T : ThetaTied D X) (Z : DivX D) :
    MeasTupleTied T Z ↔ (∀ μ, ∀ v ∈ ramPlaces T μ, IsSplit D v) ∧ PlacesTied T Z ∧ ThetaDivisorCompatibility X Z :=
  ⟨fun h => ⟨h.split, h.places, (factor_iff_myTied h.places).1 h.factor⟩,
    fun h => ⟨h.1, h.2.1, (factor_iff_myTied h.2.1).2 h.2.2⟩⟩

theorem myTied_of_measTupleTied {T : ThetaTied D X} {Z : DivX D} (h : MeasTupleTied T Z) : ThetaDivisorCompatibility X Z :=
  ((measTupleTied_iff T Z).1 h).2.2

theorem mY_ne_one {T : ThetaTied D X} (h : MeasFactor T) {μ : D.what₂.Tup} (hμ : (ramPlaces T μ).Nonempty) :
    X.mY μ 1 ≠ 1 := by
  obtain ⟨S, hS, hm⟩ := h μ
  obtain ⟨v, hv⟩ := hμ
  have h2 := D.R.two_le_m
  have hr : 0 < D.R.r := by unfold Ranks.r; omega
  have ht : 0 < 1 * D.R.t := by have := D.R.rank_add_five_le; omega
  rw [hm 1 (by omega), ← Nat.cast_prod, Ne, Nat.cast_eq_one, Finset.prod_eq_one_iff]
  intro hall
  exact localIndex_ne_one v hr ht (hall v (Finset.mem_coe.1 (hS.symm.subset hv)))

theorem myTied_not_measTupleTied (T : ThetaTied D X) (Z : DivX D) {μ : D.what₂.Tup} (hμ : (ramPlaces T μ).Nonempty) :
    ∃ (X' : ThetaX D) (T' : ThetaTied D X') (Z' : DivX D), Z'.Qp = Z.Qp ∧ (∀ ν, ramPlaces T' ν = ramPlaces T ν) ∧
      (∀ ν j, X'.mY ν j = 1) ∧ ThetaDivisorCompatibility X' Z' ∧ ¬ PlacesTied T' Z' ∧ ¬ MeasFactor T' ∧
      ¬ MeasTupleTied T' Z' := by
  have hn : ¬ PlacesTied (GlobalTheory.MeasTuple.thetaDivisorRestriction T (GlobalTheory.MeasTuple.rep Z 0)) (GlobalTheory.MeasTuple.rep Z 0) := fun h => by
    obtain ⟨e, -⟩ := h μ
    obtain ⟨v, hv⟩ := hμ
    exact (e.symm ⟨v, hv⟩).1.elim0
  exact ⟨_, GlobalTheory.MeasTuple.thetaDivisorRestriction T (GlobalTheory.MeasTuple.rep Z 0), GlobalTheory.MeasTuple.rep Z 0, rfl, fun _ => rfl,
    (GlobalTheory.MeasTuple.trivial_factor X Z).2.2, GlobalTheory.MeasTuple.myTied_setMY _ _, hn,
    fun h => mY_ne_one h (μ := μ) hμ ((GlobalTheory.MeasTuple.trivial_factor X Z).2.2 μ 1), fun h => hn h.places⟩

end GlobalTheory.MeasTupleEq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NegTraceSymplecticFormComplexStructurePos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder Kronecker

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_kron_pos {m n : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} {Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) (x : Matrix (Fin m) (Fin n) ℂ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * P i k * Q j l * x k l := by
  have h := (hP.kronecker hQ).dotProduct_mulVec_pos (x := fun p : Fin m × Fin n => x p.1 p.2)
    (fun h0 => hx (by ext i j; exact congrFun h0 (i, j)))
  convert h using 1
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Finset.mul_sum, kroneckerMap_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
  rw [Complex.star_def]; ring

theorem IsCart.adj_mul {n : ℕ} {G t : Matrix (Fin n) (Fin n) ℂ} (h : IsCart G t) :
    (t.map (starRingEnd ℂ))ᵀ * G = G * t := by
  have e : (t.map (starRingEnd ℂ))ᵀ = tᴴ := by ext i j; rfl
  rw [e]
  calc tᴴ * G = tᴴ * G * (t * t) := by rw [h.1, Matrix.mul_one]
    _ = G * t := by rw [← Matrix.mul_assoc, h.2.1]

theorem hC_actC_pos {D : D7} (V W : HSp D) (τ : D.what₂.Tau) (t : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (t' : Matrix (Fin W.rank) (Fin W.rank) ℂ) (h : IsCart (gramAt D V τ) t) (h' : IsCart (gramAt D W τ) t')
    (x : WC V W) (hx : x ≠ 0) : 0 < hC V W τ x (actC V W t t' x) := by
  unfold hC actC
  split_ifs with hr
  · have p := sum_kron_pos h.2.2.transpose h'.2.2 x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_small] at p ⊢
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    convert p using 2
    rw [← h.adj_mul]
    simp only [Matrix.mul_assoc]
  · have p := sum_kron_pos h.2.2 h'.2.2.transpose x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_large] at p ⊢
    convert p using 2
    rw [← h'.adj_mul]
    simp only [Matrix.mul_assoc]

theorem symplC_jAt_neg : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V)
    (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') →
    ∀ x : WC V W, x ≠ 0 → 0 < -symplC V W τ (jAt V W τ s s' x) x := by
  intro D V W τ s s' h h' x hx
  have p := hC_actC_pos V W τ _ _ h h' x hx
  have q := xi_zero_im_pos D τ
  unfold symplC jAt
  rw [hC_smul_right]
  obtain ⟨p1, p2⟩ := Complex.pos_iff.1 p
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, ← p2]
  nlinarith [mul_pos p1 q]

end GlobalTheory.FockCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem smooth_iff_sm_and_real_lines : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), (∀ f : WA V W → ℂ, (∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)) ↔ Sm (iotaW σ V W) f) ∧ (∀ L : ℝ →+ WA V W, IsRealDir V W L → ∀ t : ℝ, L t = iotaW σ V W (t • piW θ V W (L 1))) ∧ ∀ u : RW V W, ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ ∀ t : ℝ, L t = iotaW σ V W (t • u) := by
  intro D θ σ h V W
  refine ⟨fun f => ⟨fun H w => ?_, fun H k L hL hL0 w => ?_⟩, fun L hL t => ?_, fun u => ?_⟩
  · let e : RW V W ≃L[ℝ] (Fin (Module.finrank ℝ (RW V W)) → ℝ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
    have h1 := H _ ((iotaW σ V W).comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom)
      ((h.continuous_iota V W).comp e.symm.continuous) (fun t => h.real_iota V W _) w
    have h2 := h1.comp e.contDiff
    have h3 : (fun x : RW V W => f (w + iotaW σ V W x)) = fun x => f (w + iotaW σ V W (e.symm (e x))) := by
      funext x; rw [e.symm_apply_apply]
    rw [h3]
    exact h2
  · let M : (Fin k → ℝ) →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL)
    have h2 := (H w).comp M.contDiff
    have h3 : (fun t => f (w + L t)) = fun t => f (w + iotaW σ V W (piW θ V W (L t))) := by
      funext t; rw [h.iota_pi (hL0 t)]
    rw [h3]
    exact h2
  · let M : ℝ →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL.1)
    have h2 : M (t • (1 : ℝ)) = t • M 1 := M.map_smul t 1
    rw [smul_eq_mul, mul_one] at h2
    have h3 : piW θ V W (L t) = t • piW θ V W (L 1) := h2
    rw [← h3, h.iota_pi (hL.2 t)]
  · let M : ℝ →L[ℝ] RW V W := ContinuousLinearMap.toSpanSingleton ℝ u
    exact ⟨(iotaW σ V W).comp M.toLinearMap.toAddMonoidHom,
      ⟨(h.continuous_iota V W).comp M.continuous, fun t => h.real_iota V W _⟩, fun t => rfl⟩

end GlobalTheory.FockCompare
end

