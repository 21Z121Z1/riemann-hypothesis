import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomeomorphZeroSet
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Topology Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.AffCxPts

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} {k : ℕ}

def coords (φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)) (y : ↥(CxPts.ptsIn p (RingHom.id ℂ) U)) :
    Fin k → ℂ :=
  fun i => CxPts.ev p (RingHom.id ℂ) U (φ (MvPolynomial.X i)) y.1

theorem evHom_comp (φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U))
    (hC : ∀ a, φ (MvPolynomial.C a) = algX p U a) (y : ↥(CxPts.ptsIn p (RingHom.id ℂ) U)) :
    (CxPts.evHom y.2).comp φ = MvPolynomial.eval (coords φ y) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, hC, MvPolynomial.eval_C, ← CxPts.ev_eq y.2, CxPts.ev_algX y.2,
      RingHom.id_apply]
  · rw [RingHom.comp_apply, MvPolynomial.eval_X, coords, CxPts.ev_eq y.2]

def homAt {φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)} (hφ : Function.Surjective φ) (z : Fin k → ℂ)
    (hz : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval z)) : Γ(X, U) →+* ℂ :=
  φ.liftOfSurjective hφ ⟨MvPolynomial.eval z, hz⟩

theorem homAt_comp {φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)} (hφ : Function.Surjective φ)
    (z : Fin k → ℂ) (hz : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval z))
    (P : MvPolynomial (Fin k) ℂ) : homAt hφ z hz (φ P) = MvPolynomial.eval z P :=
  φ.liftOfSurjective_comp_apply hφ ⟨_, hz⟩ P

end GlobalTheory.AffCxPts

open GlobalTheory.AffCxPts GlobalTheory.CxPts GlobalTheory.Points in

theorem GlobalTheory.AffCxPts.homeomorph_zeroSet : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (U : X.Opens),
    IsAffineOpen U → (algX p U).FiniteType → ∃ (k : ℕ) (G : Finset (MvPolynomial (Fin k) ℂ)),
      Nonempty (↥(GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U) ≃ₜ
        ↥{z : Fin k → ℂ | ∀ P ∈ G, MvPolynomial.eval z P = 0}) := by
  intro X p U hU hft
  letI := (algX p U).toAlgebra
  obtain ⟨k, φa, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  let φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U) := φa.toRingHom
  have hφ' : Function.Surjective φ := hφ
  have hC : ∀ a, φ (MvPolynomial.C a) = algX p U a := fun a => φa.commutes a
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (RingHom.ker φ) :)
  refine ⟨k, G, ⟨?_⟩⟩
  let Z : Set (Fin k → ℂ) := {z | ∀ P ∈ G, MvPolynomial.eval z P = 0}
  have hker (z : Z) : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval (z : Fin k → ℂ)) := by
    rw [← hG]
    exact Ideal.span_le.2 fun P hP => RingHom.mem_ker.2 (z.2 P hP)
  have hψ (z : Z) (a : ℂ) : homAt hφ' z (hker z) (algX p U a) = RingHom.id ℂ a := by
    rw [← hC, homAt_comp, MvPolynomial.eval_C, RingHom.id_apply]
  let s (z : Z) : CxPts p (RingHom.id ℂ) := ofHom hU (homAt hφ' z (hker z)) (hψ z)
  have hs_ev (z : Z) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (s z) = homAt hφ' z (hker z) f :=
    ev_ofHom hU _ (hψ z) f
  have hcoords (z : Z) (i : Fin k) :
      ev p (RingHom.id ℂ) U (φ (MvPolynomial.X i)) (s z) = (z : Fin k → ℂ) i := by
    rw [hs_ev, homAt_comp, MvPolynomial.eval_X]
  have htZ (y : ↥(ptsIn p (RingHom.id ℂ) U)) : coords φ y ∈ Z := fun P hP => by
    rw [← evHom_comp φ hC y, RingHom.comp_apply,
      RingHom.mem_ker.1 (hG ▸ Ideal.subset_span hP : P ∈ RingHom.ker φ), map_zero]
  have hgen : Subring.closure (Set.range (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p U) ∪
      Set.range fun i : Fin k => φ (MvPolynomial.X i)) = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨P, rfl⟩ := hφ' f
    induction P using MvPolynomial.induction_on with
    | C a => exact Subring.subset_closure (Or.inl ⟨a, (hC a).symm⟩)
    | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
    | mul_X P i hP =>
      rw [map_mul]; exact mul_mem hP (Subring.subset_closure (Or.inr ⟨i, rfl⟩))
  have hsc : Continuous s := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    refine (PtsOver.tendsto_iff_of_generators hU (ofHom_mem hU _ (hψ z)) hgen).2
      ⟨Eventually.of_forall fun w => ofHom_mem hU _ (hψ w), ?_⟩
    rintro _ ⟨i, rfl⟩
    have e (w : Z) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (s w).1 U (φ (MvPolynomial.X i)) = (w : Fin k → ℂ) i := hcoords w i
    rw [show (fun w : Z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (s w).1 U (φ (MvPolynomial.X i))) =
        fun w : Z => (w : Fin k → ℂ) i from funext e]
    exact (e z).symm ▸ ((continuous_apply i).comp continuous_subtype_val).tendsto z
  exact
    { toFun := fun y => ⟨coords φ y, htZ y⟩
      invFun := fun z => ⟨s z, ofHom_mem hU _ (hψ z)⟩
      left_inv := fun y => by
        refine Subtype.ext (Subtype.ext (ext_of_valR hU (ofHom_mem hU _ (hψ _)) y.2 fun f => ?_))
        obtain ⟨P, rfl⟩ := hφ' f
        change ev p (RingHom.id ℂ) U (φ P) (s _) = ev p (RingHom.id ℂ) U (φ P) y.1
        rw [hs_ev, homAt_comp, ev_eq y.2, ← RingHom.comp_apply, evHom_comp φ hC y]
      right_inv := fun z => Subtype.ext (funext fun i => hcoords z i)
      continuous_toFun := by
        refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
        exact (continuousOn_iff_continuous_restrict.1 (continuousOn_ev (φ (MvPolynomial.X i))))
      continuous_invFun := hsc.subtype_mk _ }
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntOfHomAt
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV
open GlobalTheory.GO.ChRoot GlobalTheory.TopStep

namespace GlobalTheory.ColPeriod.EntQ

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem val_of_pow {a : K} {k : ℕ} (hk : 0 < k) (h : w.valuation K (a ^ k) = 1) : w.valuation K a = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le' hk.ne').1 h

theorem val_nat {q : ℕ} (hq : (q : 𝓞 K) ∉ w.asIdeal) : w.valuation K (q : K) = 1 := by
  have := (w.valuation_eq_one_iff_notMem (K := K) (r := (q : 𝓞 K))).2 hq
  simpa using this

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem val_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.unitV χ a) ≤ 1 ∧ w.valuation K (LocE.unitV χ a)⁻¹ ≤ 1 := by
  by_cases h : LocE.unitV χ a = 0
  · simp [h]
  · obtain ⟨k, hk, h1⟩ := unitV_root χ a h
    have := val_of_pow w hk (a := LocE.unitV χ a) (by rw [h1, map_one])
    simp [this]

theorem val_locChar (q : ℕ) {cq : K} (hc : w.valuation K cq = 1) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.locChar q cq χ a) ≤ 1 ∧ w.valuation K (LocE.locChar q cq χ a)⁻¹ ≤ 1 := by
  unfold LocE.locChar
  rw [mul_inv, map_mul, map_mul, map_inv₀ _ (cq ^ _), map_zpow₀, hc, one_zpow, inv_one, one_mul, one_mul]
  exact val_unitV w χ _

theorem val_om {a b : ℕ} {mu : E → K} (hmu : ∀ t, w.valuation K (mu t) ≤ 1 ∧ w.valuation K (mu t)⁻¹ ≤ 1) (v : E → ℤ)
    {sq : K} (hsq : w.valuation K sq = 1) (g₀ : (Fin a → E) ≃ₗ[E] (Fin a → E)) (h : (Fin b → E) ≃ₗ[E] (Fin b → E))
    {Φ : Loc.SF E K a b} (hΦ : ∀ x, w.valuation K (Φ x) ≤ 1) (x) : w.valuation K (Loc.om mu v sq g₀ h Φ x) ≤ 1 := by
  unfold Loc.om
  simp only [map_mul, map_zpow₀, hsq, one_zpow, mul_one]
  exact mul_le_one' (mul_le_one' (hmu _).1 (hmu _).2) (hΦ _)

theorem val_PhiQ (q : ℕ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x) :
    w.valuation K (LocE.PhiQ q χ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ
  split_ifs
  · exact (val_unitV w χ _).1
  · simp

end Val

section Supp

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_fIdx {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : ∃ s, s < n + c ∧ LocE.fIdx k₀ c n s = l := by
  refine ⟨LocE.fPos k₀ c n l, ?_, ?_⟩
  · unfold LocE.fPos
    split_ifs <;> omega
  · unfold LocE.fIdx LocE.fPos
    split_ifs <;> omega

theorem int_of_PhiQ {q : ℕ} {χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ} {k₀ r c' n' c n : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n)
    {x : HomE E (n' + c') (n + c)} (hx : LocE.PhiQ q χ k₀ r c' n' c n x ≠ 0) {v : Sp E (n' + c')}
    (hv : v ∈ stdAt E (n' + c') P) : x v ∈ stdAt E (n + c) P := by
  unfold LocE.PhiQ at hx
  split_ifs at hx with h
  · rw [mem_stdAt] at hv ⊢
    intro i
    rw [apply_eq_sum]
    refine intAt_sum _ fun j _ => (hv j).mul ?_
    obtain ⟨p, hp, e⟩ := exists_fIdx hk i.2
    obtain ⟨p', hp', e'⟩ := exists_fIdx hk' j.2
    have h1 := h.1 p p' hp hp'
    have h2 : Loc.eN E (n' + c') j.1 = Pi.single j 1 := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    simpa [LocE.entB, e, e', LocE.scE, Loc.atN, h2] using h1
  · exact absurd rfl hx

theorem intAt_chArg {n' c' n c : ℕ} (a : E) (x : HomE E (n' + c') (n + c))
    (h : ∀ v ∈ stdAt E (n' + c') P, a • x v ∈ stdAt E (n + c) P) : IntAt P (a * Loc.chArg x) := by
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero

theorem int_of_homAt {a b : ℕ} {z : HomE E a b} (hz : z ∈ homAt {P} (stdLat E a) (stdLat E b)) (B : ℕ) (s : Fin a) (l : Fin b) :
    IntAt P (((qOf P : E) ^ B)⁻¹ * (((qOf P : E) ^ B) • z) (Pi.single s 1) l) := by
  have h := mem_stdAt.1 (hz P (Finset.mem_singleton_self P) _ (single_mem_stdAt s)) l
  have hq := qOf_ne_zero (P := P)
  rwa [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]

end Supp

theorem k_le_N (R : Ranks) (j : ℕ) : R.k ≤ R.N j := by
  unfold Ranks.N
  omega

theorem entryAtQ (hV : VolumeAtQ) : EntryAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 hL P w hP hdeg hq hmu
  have hm := hL.hm
  have hqv := val_nat w hq
  have hsq : w.valuation X.K (cst.sq P) = 1 := val_of_pow w two_pos (by rw [hL.cst_ok.sq_sq, hqv])
  have hom : ∀ i, i < R.m → ∀ hal h x, w.valuation X.K (omPhi Ch sel mu cst i P hal h x) ≤ 1 := by
    intro i hi hal h x
    refine val_om w (fun t => val_locChar w _ (hmu i hi) _ t) _ hsq _ _ (fun y => ?_) x
    rw [PhiAt, if_neg hP]
    exact val_PhiQ w _ _ _ _ _ _ _ _ y
  refine ⟨fun i hi al be => ⟨fun x => ?_, fun x z hz => hL.xiInv i hi al be P x _ (int_of_homAt hz _)⟩,
    fun al y => ⟨fun x => hom m2 (by omega) _ _ _, fun x z hz => hL.psiInvX al P x _ y (int_of_homAt hz _)⟩⟩
  unfold XiAt E1at Loc.E1
  rw [map_mul, map_mul, map_pow, map_inv₀ _ (_ ^ cst.B), map_pow, hqv, one_pow, inv_one, one_pow, one_mul]
  refine mul_le_one' (hV X Pr R _ _ _ _ w hP hdeg hq) (Valuation.map_sum_le _ fun t _ => ?_)
  generalize Loc.xx1 x t = y
  by_cases h0 : omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y = 0
  · simp [h0]
  rw [map_mul]
  refine mul_le_one' (hom i (by omega) _ _ _) (le_of_eq ?_)
  have h1 := right_ne_zero_of_mul h0
  rw [PhiAt, if_neg hP] at h1
  have hb := hL.boundQ i al P hP
  have hb' := hL.boundQ (i + 1) be P hP
  have hD := hL.depthQ' P hP
  simp only [lamYat, hP, if_false, mem_lamY_zero] at hb hb'
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * Loc.chArg y) := by
    refine intAt_chArg _ y fun v hv => ?_
    have h2 := (hb' _ (int_of_PhiQ (k_le_N R _) (k_le_N R _) h1 (hb v hv).1)).2
    have h3 : (L.h i al P) ((L.h i al P)⁻¹ v) = v := LinearEquiv.apply_symm_apply _ v
    simpa [h3] using h2
  have hint' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * -Loc.chArg y) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + (i + 1) := ⟨cst.D P - (i + 1), by omega⟩
    rw [hd, pow_add, mul_neg, mul_assoc]
    exact intAt_neg ((intAt_pow (intAt_nat _) _).mul hint)
  exact val_of_pow w (pow_pos (qOf_pos _) _) (by rw [psi_root hL.cst_ok P _ hint', map_one])

end GlobalTheory.ColPeriod.EntQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapApplyEqMulVec
section
namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem map_apply_eq_mulVec {E K : Type} [Field E] [Field K] (ρ : E →+* K) {N n : ℕ}
    (f : (Fin N → E) →ₗ[E] (Fin n → E)) (x : Fin N → E) :
    (fun k => ρ (f x k)) = ((LinearMap.toMatrix' f).map ρ) *ᵥ (fun k => ρ (x k)) := by
  funext k
  rw [← LinearMap.toMatrix'_mulVec f x]
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem locSp_map {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N n : ℕ} (f : (Fin N → E) →ₗ[E] (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    locSp W ρ (Λ.map (f.restrictScalars (𝓞 E))) =
      (locSp W ρ Λ).map ((((LinearMap.toMatrix' f).map ρ).mulVecLin).restrictScalars W) := by
  unfold locSp
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact map_apply_eq_mulVec ρ f x

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLocSpOfNatCastSmulMem
section
noncomputable section

namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem mem_locSp_of_natCast_smul_mem {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N' : ℕ} (L' : Submodule (𝓞 E) (Fin N' → E)) (z : Fin N' → E) (s : ℕ) (hs : IsUnit (s : W))
    (hz : (s : E) • z ∈ L') : (fun k => ρ (z k)) ∈ locSp W ρ L' := by
  obtain ⟨u, hu'⟩ := hs
  have hmem : (fun k => ρ (((s : E) • z) k)) ∈ locSp W ρ L' := Submodule.subset_span ⟨_, hz, rfl⟩
  have e : (fun k => ρ (z k)) = ((↑u⁻¹ : W)) • (fun k => ρ (((s : E) • z) k)) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Algebra.smul_def]
    rw [← mul_assoc, ← map_natCast (algebraMap W K) s, ← hu', ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

theorem locSp_maps_of_unit_smul {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N N' : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E))
    (A : Matrix (Fin N') (Fin N) E) (s : ℕ) (hs : IsUnit (s : W)) (hA : ∀ x ∈ L, (s : E) • (A *ᵥ x) ∈ L') :
    ∀ z ∈ locSp W ρ L, (A.map ρ) *ᵥ z ∈ locSp W ρ L' := by
  intro w hw
  have h : locSp W ρ L ≤ (locSp W ρ L').comap (((A.map ρ).mulVecLin).restrictScalars W) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show (A.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ L'
    have e : (A.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((A *ᵥ x) k) := by
      funext k
      exact (RingHom.map_mulVec ρ A x k).symm
    rw [e]
    exact mem_locSp_of_natCast_smul_mem W K ρ L' _ s hs (hA x hx)
  exact h hw

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NabLeDelOfLocal
section
noncomputable section

namespace GlobalTheory.ColPeriod.WeylLoc

open NumberField IsDedekindDomain MvPolynomial Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem localized_le_of_le_localized {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    {N N' : Submodule (𝓞 K) V} (h : N ≤ localization₂ w.asIdeal N') : localization₂ w.asIdeal N ≤ localization₂ w.asIdeal N' := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, h'⟩ := h hx
  exact ⟨t * s, mul_mem ht hs, by rw [mul_smul]; exact h'⟩

omit [NumberField K] in
theorem intCast_notMem {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : (c : 𝓞 K) ∉ w.asIdeal := by
  intro ha
  have hco : IsCoprime (p : ℤ) c := (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hc
  obtain ⟨x, y, e⟩ := hco.map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at e
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ ha)))

theorem nablaSq_le_locP (h : NablaMemDeltaLocallyAtLargePrime) {n : ℕ} (lam : DomWeight n) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) (hs : lam.spread < p) :
    (nablaSq (𝓞 K) n lam).map (toK K _) ≤ localization₂ w.asIdeal ((delSq (𝓞 K) n lam).map (toK K _)) := by
  unfold nablaSq
  rw [GlobalTheory.StdDual.dualWeyl_eq, Submodule.map_span, Submodule.span_le,
    ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))]
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  have hf' : f ∈ nablaSq ℤ n lam := by
    unfold nablaSq
    rw [GlobalTheory.StdDual.dualWeyl_eq]
    exact Submodule.subset_span hf
  obtain ⟨c, hc, hcf⟩ := h n lam p hp hs f hf'
  refine ⟨(c : 𝓞 K), intCast_notMem hp w hw hc, map (Int.castRingHom (𝓞 K)) (c • f),
    GlobalTheory.TestLat.WeylLocal.map_mem_weyl _ _ hcf, ?_⟩
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul (𝓞 K), map_smul]
  rfl

theorem nabStd_le_locP (h : NablaMemDeltaLocallyAtLargePrime) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) (hs : ∀ τ, (lam τ).spread < p) :
    nabStd K lam ≤ localization₂ w.asIdeal (delStd K lam) := by
  unfold nabStd Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  exact GlobalTheory.TestLat.WeylLocal.ten_mem_locP w _ f fun τ => nablaSq_le_locP h (lam τ) hp w hw (hs τ) (hf τ)

theorem nabLeDel_of_local (h : NablaMemDeltaLocallyAtLargePrime) : GlobalTheory.ColPeriod.NabLeDel := by
  intro K _ _ ι _ n lam M hM p w hp hw hs x hx
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
  have h1 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB
  have hx' : x.1 ∈ localization₂ w.asIdeal (nabP lam M) := hx
  change x.1 ∈ localization₂ w.asIdeal (delP lam M)
  rw [h1.1] at hx'
  rw [h1.2]
  exact Submodule.map_mono (localized_le_of_le_localized w (nabStd_le_locP h lam hp w hw hs)) hx'

end GlobalTheory.ColPeriod.WeylLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
section
noncomputable section

namespace GlobalTheory.ColPeriod

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recWts)

theorem nuRow_succ_eq_wt (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.N j) :
    DV.nuRow D u (j + 1) τ n =
      ((Examples₂.wtN (D.hcW u τ) n + wG D.R ((D.hcW u τ).e ⟨j, hj⟩) (j + 1) : ℚ) : ℝ) := by
  have hw : DV.wSz D (j + 1) τ = (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dif_pos ⟨by omega, by omega⟩, D.hcW_e]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar Examples₂.wtN Examples₂.blkN
  by_cases hk : n < D.R.k
  · rw [dif_pos hk, dif_pos hk]
    unfold hcToWeightQ rhoVec wG Ranks.N
    push_cast
    ring
  · have hb : (n - D.R.k) / (D.R.t + 1) < D.R.m := by
      have hN : n < D.R.k + j * (D.R.t + 1) := hn
      have h2 : n - D.R.k < j * (D.R.t + 1) := Nat.sub_lt_left_of_lt_add (by omega) hN
      have h3 : (n - D.R.k) / (D.R.t + 1) < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h2)
      omega
    rw [dif_neg hk, dif_neg hk, dif_pos hb, dif_pos hb]
    have hnat : n = D.R.k + (n - D.R.k) / (D.R.t + 1) * (D.R.t + 1) + (n - D.R.k) % (D.R.t + 1) := by
      have := Nat.div_add_mod (n - D.R.k) (D.R.t + 1)
      rw [mul_comm] at this
      omega
    have key : (n : ℝ) = (D.R.k : ℝ) + (((n - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1)
        + (((n - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      conv_lhs => rw [hnat]
      push_cast
      ring
    unfold wG Ranks.N
    push_cast
    linear_combination key

theorem partitionSize : PartitionSize := by
  intro D EX u j hj τ
  unfold nuAbs
  show ∑ i ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) τ i = _
  rw [Finset.sum_range, Int.cast_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [nuRow_succ_eq_wt D u j hj τ a a.2]
  have h1 := Wts.nuW_eq (recWts EX) u hj τ a
  have h2 := lamOf_wtN ((recWts EX).hc u τ) hj.le a
  have h3 : (((recWts EX).nuW u (j + 1) τ).w a : ℝ) = ((((recWts EX).nuW u (j + 1) τ).w a : ℚ) : ℝ) := by
    simp
  rw [h3, h1]
  unfold Wts.lamN
  rw [h2]
  rfl

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelMapsStepWeightValues
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

theorem evG_id_smul {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (a : ℂ) (P : Pol ℂ ι n) :
    evG fr sh (RingHom.id ℂ) (a • P) = a • evG fr sh (RingHom.id ℂ) P := by
  funext y
  simp only [evG, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply]
  ring

theorem Kmap_isVal : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)) f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → IsVal (O.frm (i + 1)) (lamTG M (i + 1)) (RingHom.id ℂ) (C.Kmap i c c' f) := by
  intro D u C A Pm M O i hi hU c c' f hf
  obtain ⟨P, hP, rfl⟩ := hf
  obtain ⟨n, h1, h2, h3, h4⟩ := GlobalTheory.T.trueWeight_consecutive_steps_partition D u C A Pm M i hi
  have hle : D.R.N i ≤ D.R.N (i + 1) := by
    unfold Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have key := GlobalTheory.KerWt.tied_on_models D u C O i hi (nuT D u i) hU ℂ (RingHom.id ℂ) (lamTG M i) n h1 c c'
    (jetC O.dgen (O.Th i c c')) 1 (fun m => by simp) (fun τ => (lamTG M i τ).detShift) h2 P hP
  rw [one_smul] at key
  have hsh : (fun τ => -C.sDiv i τ) = fun τ => (lamTG M (i + 1) τ).detShift := funext fun τ => (h4 τ).symm
  rw [hsh] at key
  refine ⟨(C.rhoDet i c * C.rhoDet' i c') • jetMap (jetC O.dgen (O.Th i c c')) n P, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (GlobalTheory.KerWt.jet_in_vv_of_weight ℂ D.what₂.Tau _ _ hle (lamTG M i) (lamTG M (i + 1)) n h3 _ P hP)
  · rw [key, evG_id_smul]

end GlobalTheory.KerJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents : ∀ {D : D7} (V : HSp D), (∀ f : Formalism.L2.Theta.AE D, f * f = f → cA D f = f → (∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g) ∧ (∀ g : GA D V, ∃ g₁ g₂, SuppF V f g₁ ∧ SuppF V (1 - f) g₂ ∧ g = g₁ * g₂) ∧ ∀ f' g g', f * f' = 0 → SuppF V f g → SuppF V f' g' → Commute g g') ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → f * f = f ∧ cA D f = f ∧ (∀ g, SuppF V f g → g ∈ GfC V) ∧ (∀ e' f', IsPrimeIdem P e' f' → e' = e ∧ f' = f) ∧ ∀ P' e' f', IsPrimeIdem P' e' f' → f * f' = 0 ∨ (f' = f ∧ (P' = P ∨ Formalism.IndefR.Lev.IsConjPl P P'))) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) P' e, IsIdemAt e P → Formalism.IndefR.Lev.IsConjPl P P' → IsIdemAt (cA D e) P' := by
  first | exact @GlobalTheory.IdemSupport.supported_group_and_prime_idempotents | exact GlobalTheory.IdemSupport.supported_group_and_prime_idempotents | (intros; apply GlobalTheory.IdemSupport.supported_group_and_prime_idempotents <;> assumption)
end

