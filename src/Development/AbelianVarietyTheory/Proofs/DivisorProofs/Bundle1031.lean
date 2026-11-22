import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelDatum

variable {D : D7}

def rowP (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x : Fin W.rank → D.host.E) (a : Fin W.rank) : EAf D :=
  toEAf D e * ∑ k, eToEAf D (∑ l, D.sp.cm.sig (x l) * W.gram l k) * β.val k a

theorem rowPairing_add (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x y : Fin W.rank → D.host.E) (a : Fin W.rank) :
    rowP W β e (x + y) a = rowP W β e x a + rowP W β e y a := by
  simp only [rowP, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]

theorem rowPairing_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (a : Fin W.rank) :
    rowP W β e 0 a = 0 := by
  simp only [rowP, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, mul_zero]

theorem rowPairing_smul (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (c : D.host.E) (x : Fin W.rank → D.host.E)
    (a : Fin W.rank) : rowP W β e (c • x) a = eToEAf D (D.sp.cm.sig c) * rowP W β e x a := by
  simp only [rowP, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem uMat_eq (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (β : GL (Fin W.rank) (EAf D)) (e : AE D)
    (X : Fin V.rank → Fin W.rank → D.host.E) (b : Fin V.rank) (a : Fin W.rank) :
    FWT.uMat V W βV β e X b a = ∑ b', (βV⁻¹).val b b' * rowP W β e (X b') a := by
  simp only [FWT.uMat, rowP, hV, inv_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eToEAf_int (c : 𝓞 D.host.E) : eToEAf D (c : D.host.E) = (oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) := rfl

theorem exists_sig (c : 𝓞 D.host.E) : ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E) :=
  ⟨⟨_, (RingOfIntegers.isIntegral_coe c).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩

theorem rowP_int (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (hβ : IsSDFrame W β Λ 1) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (x : Fin W.rank → D.host.E) (hx : x ∈ latG W 1) (a : Fin W.rank) :
    rowP W β e x a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [rowPairing_smul, rowP, ← mul_assoc, mul_comm _ (toEAf D e)]
    exact mul_mem (GlobalTheory.IdemIntegral.conj_mem_intAf D e P he hP c hc) (GlobalTheory.PairIntegral.pair_mem_intAf D W β Λ hβ v hv a)
  | zero => rw [rowPairing_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [rowPairing_add]; exact add_mem hx hy
  | smul c x _ hx =>
    obtain ⟨c', hc'⟩ := exists_sig c
    rw [show c • x = (c : D.host.E) • x from rfl, rowPairing_smul, ← hc', eToEAf_int]
    exact mul_mem (Subtype.prop _) hx

theorem residue_rowPairing_eq_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (a : Fin W.rank)
    (hi : ∀ x, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x : La) (hx : x ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) : resS D.host.F PP ⟨_, hi x⟩ = 0 := by
  refine Submodule.smul_induction_on (p := fun x => resS D.host.F PP ⟨_, hi x⟩ = 0) hx (fun c hc y _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨c', hc', e'⟩ := hJ c hc
    have : (⟨_, hi (c • y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = oToS D.host.F D.host.E c' * ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (c • y)) a = eToEAf D (c' : D.host.E) * rowP W β e (ι y) a
      rw [map_smul, show c • ι y = (c : D.host.E) • ι y from rfl, rowPairing_smul, e']
    rw [this, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hc', zero_mul]
  · have : (⟨_, hi (x + y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi x⟩ + ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (x + y)) a = rowP W β e (ι x) a + rowP W β e (ι y) a
      rw [map_add, rowPairing_add]
    rw [this, map_add, hx, hy, add_zero]

theorem redM_uMat (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) (X : Fin V.rank → Fin W.rank → D.host.E)
    (hi : ∀ b a, rowP W β e (X b) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    IsIntM (FWT.uMat V W βV β e X) ∧ ∀ PP b a, redM PP (FWT.uMat V W βV β e X) b a =
      ∑ b', resS D.host.F PP ⟨_, hβ b b'⟩ * resS D.host.F PP ⟨_, hi b' a⟩ := by
  have h : IsIntM (FWT.uMat V W βV β e X) := fun b a => by
    rw [uMat_eq V W hV]
    exact sum_mem fun b' _ => mul_mem (hβ b b') (hi b' a)
  refine ⟨h, fun PP b a => ?_⟩
  rw [redM, dif_pos (h b a)]
  simp only [← map_mul, ← map_sum]
  congr 1
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_finsetSum]
  exact uMat_eq V W hV βV β e X b a

theorem omega_congr {a b : ℕ} (Pg Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (h : ∀ PP, PP ∈ Pg ∨ PP ∈ Q → y PP = y' PP) :
    omegaK Pg y * omegaQ Q r ξ k y = omegaK Pg y' * omegaQ Q r ξ k y' := by
  classical
  have h1 : omegaK Pg y = omegaK Pg y' := by
    unfold omegaK
    refine if_congr (forall₂_congr fun PP hPP => by rw [h PP (Or.inl hPP)]) rfl rfl
  have h2 : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
    have e : (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) ↔
        ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det :=
      forall₂_congr fun PP hPP => by rw [h PP (Or.inr hPP)]
    unfold omegaQ
    by_cases c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dif_pos c, dif_pos (e.1 c)]
      refine Finset.prod_congr rfl fun PP _ => ?_
      have : (c PP.1 PP.2).2.unit = (e.1 c PP.1 PP.2).2.unit := Units.ext (by
        rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 (Or.inr PP.2)])
      rw [this]
    · rw [dif_neg c, dif_neg (fun c' => c (e.2 c'))]
  rw [h1, h2]

theorem exists_omega_field (Pg Q : Finset (Pl D.host.E)) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
      (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), omegaK Pg y * omegaQ Q r ξ k y ∈ M := by
  have hf : ∀ PP : Pl D.host.E, 0 < Nat.card (kP PP)ˣ := fun PP => by
    have : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
    exact Nat.card_pos
  obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.FrameVal.exists_roots (∏ PP ∈ Q, Nat.card (kP PP)ˣ) (Finset.prod_pos fun PP _ => hf PP)
  refine ⟨M, hM, fun r ξ k y => mul_mem ?_ ?_⟩
  · unfold omegaK
    split_ifs
    exacts [one_mem _, zero_mem _]
  · unfold omegaQ
    split_ifs
    · refine prod_mem fun PP _ => zpow_mem (h _ ?_) _
      obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Nat.card (kP PP)ˣ) PP.2
      rw [hu, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]
    · exact zero_mem _

set_option maxHeartbeats 800000 in

theorem exists_datum (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (hi : ∀ x a, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x z : Fin V.rank → La) (h : ∀ b, z b - x b ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) :
    redM PP (FWT.uMat V W βV β e fun b => ι (z b)) = redM PP (FWT.uMat V W βV β e fun b => ι (x b)) := by
  have key : ∀ b' a, resS D.host.F PP ⟨_, hi (z b') a⟩ = resS D.host.F PP ⟨_, hi (x b') a⟩ := fun b' a => by
    have h2 := residue_rowPairing_eq_zero W β e ι a (fun x => hi x a) J PP hJ _ (h b')
    have : (⟨_, hi (z b') a⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi (z b' - x b') a⟩ + ⟨_, hi (x b') a⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (z b')) a = rowP W β e (ι (z b' - x b')) a + rowP W β e (ι (x b')) a
      rw [← rowPairing_add, ← LinearMap.map_add, sub_add_cancel]
    rw [this, RingHom.map_add, h2, zero_add]
  funext b a
  exact ((redM_uMat V W hV βV hβ β e (fun b => ι (z b)) fun b a => hi (z b) a).2 PP b a).trans
    ((Finset.sum_congr rfl fun b' _ => congrArg _ (key b' a)).trans
      ((redM_uMat V W hV βV hβ β e (fun b => ι (x b)) fun b a => hi (x b) a).2 PP b a).symm)

set_option maxHeartbeats 1000000 in

theorem exists_phi : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_vP → ∀ (i : Fin D.R.m), VStd D i → ∀ (t : T0) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ J : Ideal (𝓞 D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) → ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M', PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hlev hvP i hV t La _ _ ι hι
  obtain ⟨M, hM, hv⟩ := exists_omega_field R.Pg (R.Q t)
  refine ⟨M, hM, fun M' hle hP J hJ => ?_⟩
  obtain ⟨-, e, he, -⟩ := hvP i t
  have hβ := GlobalTheory.StdFrameInv.isIntM_inv D i _ _ hV (hlev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hlev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hle (hv (Wc D i).rank (R.xiR t) (-1) fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out))⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)

end GlobalTheory.LevelDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisAtPrimeOfIsLattice
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem exists_valuation_bound_of_fg {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) :
    ∃ C : WithZero (Multiplicative ℤ), ∀ x ∈ L, ∀ i, w.valuation E (x i) ≤ C := by
  classical
  obtain ⟨s, rfl⟩ := hL
  refine ⟨(s ×ˢ (Finset.univ : Finset (Fin n))).sup fun p => w.valuation E (p.1 p.2), ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro i
    exact Finset.le_sup (f := fun p : (Fin n → E) × Fin n => w.valuation E (p.1 p.2))
      (b := (x, i)) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; exact Valuation.map_add_le _ (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (w.valuation_le_one a)).trans (hx i)

theorem valuation_det_le_pow_of_entry_le {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (X : Matrix (Fin n) (Fin n) E)
    {C : WithZero (Multiplicative ℤ)} (h : ∀ i j, w.valuation E (X i j) ≤ C) :
    w.valuation E X.det ≤ C ^ n := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  have h1 : w.valuation E ((Equiv.Perm.sign σ : ℤ) : E) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine (mul_le_of_le_one_left' h1).trans ?_
  calc ∏ i, w.valuation E (X (σ i) i) ≤ ∏ _i : Fin n, C :=
        Finset.prod_le_prod' fun i _ => h _ _
    _ = C ^ n := by simp

theorem exists_det_ne_zero_col_mem_of_span_eq_top {E : Type} [Field E] {n : ℕ}
    {S : Set (Fin n → E)} (hS : Submodule.span E S = ⊤) :
    ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ ∀ j, (fun i => X i j) ∈ S := by
  classical
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent E S
  rw [hS] at hspan
  let b : Module.Basis t E (Fin n → E) := Module.Basis.mk hli (by simp [hspan])
  have hfin : Finite t := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  have hc : Fintype.card t = n := by
    rw [← Module.finrank_eq_card_basis b]; simp
  let e : t ≃ Fin n := Fintype.equivFinOfCardEq hc
  let b' := b.reindex e
  refine ⟨Matrix.of fun i j => b' j i, ?_, fun j => ?_⟩
  · have hli' : LinearIndependent E (Matrix.of fun i j => b' j i).col := b'.linearIndependent
    have := Matrix.linearIndependent_cols_iff_isUnit.1 hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  · have : (fun i => (Matrix.of fun i j => b' j i) i j) = (e.symm j : Fin n → E) := by
      funext i; simp [b', b]
    rw [this]
    exact htS (e.symm j).2

theorem exists_local_basis_of_isLattice (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) :
    ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  classical
  obtain ⟨C, hC⟩ := exists_valuation_bound_of_fg w hL.fg
  obtain ⟨X₀, hX₀, hX₀L⟩ := exists_det_ne_zero_col_mem_of_span_eq_top hL.span_eq_top
  have hbd : ∀ X : Matrix (Fin n) (Fin n) E, (∀ j, (fun i => X i j) ∈ L) →
      w.valuation E X.det ≤ C ^ n := fun X hX =>
    valuation_det_le_pow_of_entry_le w X fun i j => hC _ (hX j) i
  obtain ⟨m, ⟨X, hX, hXL, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      WithZero.log (w.valuation E X.det) = m)
    ⟨WithZero.log (C ^ n), by
      rintro _ ⟨X, hX, hXL, rfl⟩
      have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
      have h1 := hbd X hXL
      have h2 : C ^ n ≠ 0 := fun h => h0 (le_antisymm (h ▸ h1) zero_le')
      exact (WithZero.log_le_log h0 h2).2 h1⟩
    ⟨_, X₀, hX₀, hX₀L, rfl⟩
  have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
  refine ⟨X, hX.isUnit, hXL, fun x hx i => ?_⟩
  have hcr : X.det * (X⁻¹ *ᵥ x) i = (X.updateCol i x).det := by
    have := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer X x hX.isUnit) i
    simpa [Matrix.cramer_apply] using this
  have hle : w.valuation E (X.updateCol i x).det ≤ w.valuation E X.det := by
    by_cases hY : (X.updateCol i x).det = 0
    · simp [hY]
    · have h1 : w.valuation E (X.updateCol i x).det ≠ 0 := by simpa using hY
      refine (WithZero.log_le_log h1 h0).1 (hmax _ ⟨_, hY, fun j => ?_, rfl⟩)
      by_cases hj : j = i
      · subst hj
        simpa using hx
      · simpa [Matrix.updateCol_ne hj] using hXL j
  rw [← hcr, map_mul] at hle
  have hpos : 0 < w.valuation E X.det := zero_lt_iff.2 h0
  exact (mul_le_iff_le_one_right hpos).1 hle

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogPeriodFamily
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem GlobalTheory.AbsLattice.exists_unit_of_conj_stable : ∀ {A B : Type} [Ring A] [CommRing B] (j : B →+* A) (Λ : Set A) (R : Set B) (r : ℕ) (e : Fin r → A),
    (0 : A) ∈ Λ → (1 : A) ∈ Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, x + y ∈ Λ) → (∀ x ∈ Λ, -x ∈ Λ) →
    (∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) →
    (0 : B) ∈ R → (1 : B) ∈ R → (∀ x ∈ R, ∀ y ∈ R, x + y ∈ R) → (∀ x ∈ R, -x ∈ R) →
    (∀ x ∈ R, ∀ y ∈ R, x * y ∈ R) →
    (∀ a : A, ∃! β : Fin r → B, a = ∑ i, j (β i) * e i) →
    (∀ β : Fin r → B, (∑ i, j (β i) * e i ∈ Λ) ↔ ∀ i, β i ∈ R) →
    (∀ i i' : Fin r, ∃ (N : ℕ) (ρ : Fin N → B) (μ : Fin N → A), (∀ k, ρ k ∈ R) ∧ (∀ k, μ k ∈ Λ) ∧
      ∀ β : Fin r → B, ∑ k, j (ρ k) * (∑ i'', j (β i'') * e i'') * μ k = j (β i') * e i) →
    (∀ a : A, ∃ D : ℤ, D ≠ 0 ∧ (D : A) * a ∈ Λ) →
    (∀ I : Set B, (0 : B) ∈ I → (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ ∈ R, ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x ∈ R, (D : B) * x ∈ I) ∧ ∀ x ∈ I, (D : B) * x ∈ R) →
      ∃ m : Bˣ, ∀ x, x ∈ I ↔ ∃ ρ ∈ R, x = ↑m * ρ) →
    ∀ X : Aˣ, (∀ ρ ∈ R, (X : A) * j ρ * ↑X⁻¹ ∈ Λ) → ∃ m : Bˣ, (X : A) * j ↑m ∈ Λ ∧ j ↑m⁻¹ * ↑X⁻¹ ∈ Λ := by

  intro A B _ _ j Λ R r e h0 h1 hadd hneg hmul hR0 hR1 hRadd hRneg hRmul hrep hmem hE hden hsq X hX
  rcases r with _ | n
  · have hall : ∀ a : A, a = 0 := fun a => by
      obtain ⟨β, hβ, -⟩ := hrep a
      simpa using hβ
    have key : ∀ a : A, a ∈ Λ := fun a => by rw [hall a]; exact h0
    exact ⟨1, key _, key _⟩
  ·
    have hL : ∀ ρ ∈ R, ∀ x : A, (X : A) * x ∈ Λ → (X : A) * (j ρ * x) ∈ Λ := by
      intro ρ hρ x hx
      have : (X : A) * (j ρ * x) = ((X : A) * j ρ * ↑X⁻¹) * ((X : A) * x) := by
        simp [mul_assoc]
      rw [this]; exact hmul _ (hX ρ hρ) _ hx
    have hRt : ∀ μ ∈ Λ, ∀ x : A, (X : A) * x ∈ Λ → (X : A) * (x * μ) ∈ Λ := by
      intro μ hμ x hx
      rw [← mul_assoc]; exact hmul _ hx _ hμ
    have hS : ∀ (N : ℕ) (f : Fin N → A), (∀ k, (X : A) * f k ∈ Λ) → (X : A) * ∑ k, f k ∈ Λ := by
      intro N f hf
      rw [Finset.mul_sum]
      exact Finset.sum_induction _ (· ∈ Λ) (fun a b ha hb => hadd a ha b hb) h0 (fun k _ => hf k)
    have hsingle : ∀ b : B, ∑ i'', j ((Pi.single (0 : Fin (n+1)) b : Fin (n+1) → B) i'') * e i'' = j b * e 0 := by
      intro b
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi, map_zero, zero_mul]
      · simp
    have hsingleR : ∀ b : B, j b * e 0 ∈ Λ ↔ b ∈ R := by
      intro b
      rw [← hsingle, hmem]
      constructor
      · intro h; simpa using h 0
      · intro hb i
        by_cases hi : i = 0
        · subst hi; simpa using hb
        · rw [Pi.single_eq_of_ne hi]; exact hR0
    have he0 : e 0 ∈ Λ := by
      have := (hsingleR 1).2 hR1
      rwa [map_one, one_mul] at this

    have hA : ∀ β : Fin (n+1) → B, (X : A) * (∑ i, j (β i) * e i) ∈ Λ →
        ∀ i', (X : A) * (j (β i') * e 0) ∈ Λ := by
      intro β hx i'
      obtain ⟨N, ρ, μ, hρ, hμ, hf⟩ := hE 0 i'
      rw [← hf β]
      exact hS N _ (fun k => hRt (μ k) (hμ k) _ (hL _ (hρ k) _ hx))

    have hB : ∀ b : B, (X : A) * (j b * e 0) ∈ Λ → ∀ i, (X : A) * (j b * e i) ∈ Λ := by
      intro b hb i
      obtain ⟨N, ρ, μ, hρ, hμ, hf⟩ := hE i 0
      have h := hf (Pi.single 0 b)
      rw [hsingle, Pi.single_eq_same] at h
      rw [← h]
      exact hS N _ (fun k => hRt (μ k) (hμ k) _ (hL _ (hρ k) _ hb))
    have hsum : ∀ β : Fin (n+1) → B, (∀ i, (X : A) * (j (β i) * e 0) ∈ Λ) →
        (X : A) * (∑ i, j (β i) * e i) ∈ Λ :=
      fun β hβ => hS _ _ (fun i => hB _ (hβ i) i)
    have hRint : ∀ z : ℤ, (z : B) ∈ R := by
      intro z
      induction z using Int.induction_on with
      | zero => simpa using hR0
      | succ i ih => rw [Int.cast_add, Int.cast_one]; exact hRadd _ ih _ hR1
      | pred i ih =>
        have : ((-(i : ℤ) - 1 : ℤ) : B) = ((-(i : ℤ) : ℤ) : B) + -1 := by push_cast; ring
        rw [this]; exact hRadd _ ih _ (hRneg _ hR1)
    obtain ⟨D₁, hD₁, hD₁m⟩ := hden (X : A)
    obtain ⟨D₂, hD₂, hD₂m⟩ := hden (↑X⁻¹ : A)
    have hDR : ∀ ρ ∈ R, (X : A) * (j (ρ * D₁) * e 0) ∈ Λ := by
      intro ρ hρ
      rw [map_mul, map_intCast, mul_assoc]
      apply hL ρ hρ
      rw [← mul_assoc, ← (Int.cast_commute D₁ (X : A)).eq]
      exact hmul _ hD₁m _ he0
    have hDI : ∀ β : B, (X : A) * (j β * e 0) ∈ Λ → β * D₂ ∈ R := by
      intro β hβ
      rw [← hsingleR]
      have : j (β * D₂) * e 0 = ((D₂ : A) * ↑X⁻¹) * ((X : A) * (j β * e 0)) := by
        rw [map_mul, map_intCast, ← (Int.cast_commute D₂ (j β)).eq, mul_assoc, mul_assoc,
          Units.inv_mul_cancel_left]
      rw [this]; exact hmul _ hD₂m _ hβ
    obtain ⟨m, hm⟩ := hsq {β | (X : A) * (j β * e 0) ∈ Λ}
      (by show (X : A) * (j 0 * e 0) ∈ Λ; simpa using h0)
      (fun x hx y hy => by
        show (X : A) * (j (x + y) * e 0) ∈ Λ
        rw [map_add, add_mul, mul_add]; exact hadd _ hx _ hy)
      (fun ρ hρ x hx => by
        show (X : A) * (j (ρ * x) * e 0) ∈ Λ
        rw [map_mul, mul_assoc]; exact hL ρ hρ _ hx)
      ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂,
        fun x hx => by
          show (X : A) * (j (((D₁ * D₂ : ℤ) : B) * x) * e 0) ∈ Λ
          have : ((D₁ * D₂ : ℤ) : B) * x = (D₂ : B) * (x * D₁) := by push_cast; ring
          rw [this, map_mul, mul_assoc]
          exact hL _ (hRint D₂) _ (hDR x hx),
        fun x hx => by
          have : ((D₁ * D₂ : ℤ) : B) * x = (D₁ : B) * (x * D₂) := by push_cast; ring
          rw [this]
          exact hRmul _ (hRint D₁) _ (hDI x hx)⟩
    refine ⟨m, ?_, ?_⟩
    · obtain ⟨γ, hγ, -⟩ := hrep 1
      have hγR : ∀ i, γ i ∈ R := (hmem γ).1 (hγ ▸ h1)
      have hjm : j (m : B) = ∑ i, j ((m : B) * γ i) * e i := by
        conv_lhs => rw [← mul_one (j (m : B)), hγ]
        rw [Finset.mul_sum]
        simp only [map_mul, mul_assoc]
      rw [hjm]
      exact hsum _ (fun i => (hm _).2 ⟨γ i, hγR i, rfl⟩)
    · obtain ⟨β, hβ, -⟩ := hrep (↑X⁻¹ : A)
      have hXinv : (X : A) * (∑ i, j (β i) * e i) ∈ Λ := by
        rw [← hβ, Units.mul_inv]; exact h1
      have hc : ∀ i, ∃ ρ ∈ R, β i = (m : B) * ρ := fun i => (hm _).1 (hA β hXinv i)
      choose ρ hρR hρeq using hc
      have : j (↑m⁻¹ : B) * (↑X⁻¹ : A) = ∑ i, j (ρ i) * e i := by
        rw [hβ, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← mul_assoc, ← map_mul, hρeq, ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]; exact (hmem ρ).2 hρR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CommonModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.CommonModel.isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s) : IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.CommonModel.exists_common {R : Type} [CommRing R] {Y W₀ : Scheme.{0}}
    (s₀ : W₀ ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (hs₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s₀) (i₀ : Y ⟶ W₀)
    {ι : Type} (P : ι → Scheme.{0}) (p : ∀ i, P i ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (f : ∀ i, Y ⟶ P i)
    (hp : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (p i))
    (hf : ∀ i, f i ≫ p i = i₀ ≫ s₀) (S : Finset ι) :
    ∃ (W : Scheme.{0}) (h : Y ⟶ W) (r : W ⟶ W₀), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (r ≫ s₀) ∧ h ≫ r = i₀ ∧
      ∀ i ∈ S, ∃ g : W ⟶ P i, h ≫ g = f i ∧ g ≫ p i = r ≫ s₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨W₀, i₀, 𝟙 W₀, by simpa using hs₀, by simp, by simp⟩
  | insert j S _ ih =>
    obtain ⟨W, h, r, hr, hhr, hg⟩ := ih
    have hc : h ≫ (r ≫ s₀) = f j ≫ p j := by
      rw [← Category.assoc, hhr, hf]
    refine ⟨pullback (r ≫ s₀) (p j), pullback.lift h (f j) hc, pullback.fst _ _ ≫ r, ?_, ?_, ?_⟩
    · rw [Category.assoc]
      exact _root_.GlobalTheory.ProjSpace.isProjOver_pullback hr (hp j)
    · rw [← Category.assoc, pullback.lift_fst, hhr]
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨pullback.snd _ _, pullback.lift_snd _ _ _, ?_⟩
        rw [Category.assoc, ← pullback.condition]
      · obtain ⟨g, hg₁, hg₂⟩ := hg i hi
        refine ⟨pullback.fst _ _ ≫ g, ?_, ?_⟩
        · rw [← Category.assoc, pullback.lift_fst, hg₁]
        · rw [Category.assoc, hg₂, Category.assoc]

end GlobalTheory.CommonModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicPowMulMemTensorUnramifiedIntegersStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padic_pow_mul_mem_tensorUnramifiedIntegers : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : KQ p K r), ∃ k : ℕ, (p : KQ p K r) ^ k * x ∈ intKQ p K r := by
  first | (exact @GlobalTheory.LKRes.exists_pow_mul_mem_intKQ) | (exact GlobalTheory.LKRes.exists_pow_mul_mem_intKQ) | (intros; apply GlobalTheory.LKRes.exists_pow_mul_mem_intKQ  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement
section
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p → ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  first | (exact @GlobalTheory.ratDen_pow_of_intAfP) | (exact GlobalTheory.ratDen_pow_of_intAfP) | (intros; apply GlobalTheory.ratDen_pow_of_intAfP  <;> assumption)
end

