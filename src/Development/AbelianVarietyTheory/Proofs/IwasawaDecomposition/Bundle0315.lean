import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAdmissibleUnitaryMemSupIsotypicParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReGLMemLevelVL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TwistLevel

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reGL_rfl_apply {a : ℕ} {R : Type} [CommRing R] (x : GL (Fin a) R) : reGL (rfl : a = a) R x = x := by
  ext i j
  rfl

theorem reL_rfl' {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_mem_UPts (σ : E →ₐ[F] E) {a b : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E) (J : Matrix (Fin b) (Fin b) E)
    (hJ : J = G.reindex (finCongr h) (finCongr h)) (R : Type) [CommRing R] [Algebra F R] (x : GL (Fin a) (E ⊗[F] R)) :
    reGL h _ x ∈ UPts σ J R ↔ x ∈ UPts σ G R := by
  subst h
  subst hJ
  rw [reGL_rfl_apply]
  simp only [finCongr_refl, Matrix.reindex_refl_refl]

theorem reGL_mem_levelVL (σ : E →ₐ[F] E) {a b : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E) (J : Matrix (Fin b) (Fin b) E)
    (hJ : J = G.reindex (finCongr h) (finCongr h)) (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin a → E))
    (x : GL (Fin a) (E ⊗[F] v.adicCompletion F)) :
    reGL h _ x ∈ levelVL σ J v (reL h L) ↔ x ∈ levelVL σ G v L := by
  subst h
  subst hJ
  rw [reGL_rfl_apply, reL_rfl']
  simp only [finCongr_refl, Matrix.reindex_refl_refl]

theorem exists_off (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hκ : κ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ Q, bc (prV (E := E) v) y = 1) ∧
      ∀ v, v ∉ Q → bc (prV (E := E) v) y = bc (prV (E := E) v) κ := by
  classical

  have key : ∀ (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v w : HeightOneSpectrum (𝓞 F)), w ≠ v →
      bc (prV (E := E) w) (Formalism.UG.P.afsplitU v 1 y) = bc (prV (E := E) w) y := by
    intro y v w hw
    apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe,
      Formalism.UG.P.afsplitC_prV_ne v w hw]
  induction Q using Finset.induction_on with
  | empty => exact ⟨κ, hκ, by simp, fun v _ => rfl⟩
  | @insert v Q hv ih =>
    obtain ⟨y, hy, h1, h2⟩ := ih
    refine ⟨Formalism.UG.P.afsplitU v 1 y, Formalism.UG.P.afsplitU_mem v σ J _ _ (one_mem _) hy, ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · subst hwv
        exact Formalism.UG.P.afsplit_right1 w 1 y
      · rw [key y v w hwv]
        exact h1 w ((Finset.mem_insert.mp hw).resolve_left hwv)
    · intro w hw
      have hwv : w ≠ v := fun e => hw (e ▸ Finset.mem_insert_self v Q)
      rw [key y v w hwv]
      exact h2 w (fun h => hw (Finset.mem_insert_of_mem h))

end Gen

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ}

open Classical in

def ulocQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) :=
  if h : v ∈ Q then W v h else H0.Uloc v

theorem ulocQ_pos (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ Q) :
    ulocQ H0 Q W v = W v h := by
  unfold ulocQ
  exact dif_pos h

theorem ulocQ_neg (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ Q) :
    ulocQ H0 Q W v = H0.Uloc v := by
  unfold ulocQ
  exact dif_neg h

def uQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) :
    Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)) where
  carrier := {x | x ∈ Formalism.L2.Herm.UAf hc S ∧ ∀ v, bc (prV (E := E) v) x ∈ ulocQ H0 Q W v}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun v => by rw [map_mul]; exact mul_mem (hx.2 v) (hy.2 v)⟩
  one_mem' := ⟨one_mem _, fun v => by rw [map_one]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun v => by rw [map_inv]; exact inv_mem (hx.2 v)⟩

def mkLevQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (hWl : ∀ v hv, W v hv ≤ levelVL hc.sig S.gram v H0.Lb)
    (hWQ : ∀ v hv, ∃ N : ℕ, 0 < N ∧ ∀ x, Formalism.L2.Herm.InPrinc hc S v N H0.Lb x → x ∈ W v hv)
    (hQg : ∀ v ∈ Q, ∀ i, (gp i : 𝓞 F) ∉ v.asIdeal) (hQT : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal) :
    Formalism.L2.Herm.StepLevelQ hc S gp T f Q where
  Lb := H0.Lb
  Lb_fin := H0.Lb_fin
  Lb_span := H0.Lb_span
  Lb_int := H0.Lb_int
  Lb_dual := H0.Lb_dual
  Lb_index := H0.Lb_index
  Uloc := ulocQ H0 Q W
  Uloc_lev v := by
    by_cases h : v ∈ Q
    · rw [ulocQ_pos H0 Q W h]; exact hWl v h
    · rw [ulocQ_neg H0 Q W h]; exact H0.Uloc_lev v
  Uloc_hyp v h0 h1 hT hQ := by rw [ulocQ_neg H0 Q W hQ]; exact H0.Uloc_hyp v h0 h1 hT
  Uloc_g i v h x hx := by
    rw [ulocQ_neg H0 Q W (fun hq => hQg v hq i h)]; exact H0.Uloc_g i v h x hx
  UlocAlt v h x := by
    rw [ulocQ_neg H0 Q W (fun hq => hQT v hq h)]; exact H0.UlocAlt v h x
  Uloc_Q v hv := by
    obtain ⟨N, hN, h⟩ := hWQ v hv
    exact ⟨N, hN, fun x hx => by rw [ulocQ_pos H0 Q W hv]; exact h x hx⟩
  U := uQ H0 Q W
  U_eq _ := Iff.rfl

end Lev

end GlobalTheory.Mem.Col2.TwistLevel

end

namespace GlobalTheory.Mem.Col2.TwistLevel

section Abs

def actOfRed {G : Type} [Group G] {ι : Type} {n : ℕ} {k : ι → Type} [∀ i, CommRing (k i)]
    (ρ : G → ∀ i, Matrix (Fin n) (Fin n) (k i)) (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = ρ a * ρ b) :
    MulAction G (∀ i, Fin n → k i) where
  smul a y i := ρ a i *ᵥ y i
  one_smul y := by
    funext i
    show ρ 1 i *ᵥ y i = y i
    rw [h1, Pi.one_apply, Matrix.one_mulVec]
  mul_smul a b y := by
    funext i
    show ρ (a * b) i *ᵥ y i = ρ a i *ᵥ (ρ b i *ᵥ y i)
    rw [hm, Pi.mul_apply, Matrix.mulVec_mulVec]

theorem assemble {G : Type} [Group G] {Ch : Type} [Finite Ch] {Qt : Type} [Finite Qt] (Wq : Qt → Type) [∀ q, Group (Wq q)]
    (zQ : G →* ∀ q, Wq q) (Kc : Ch → ∀ q, Subgroup (Wq q)) (hfi : ∀ β q, (Kc β q).FiniteIndex) {V : Type} [Finite V]
    [MulAction G V] (w : Ch → V) (H : Ch → Subgroup G)
    (hH : ∀ β κ, κ ∈ H β ↔ (∀ q, zQ κ q ∈ Kc β q) ∧ κ • w β = w β) :
    ∃ (Yb : Type) (_ : Finite Yb) (_ : MulAction G Yb) (yb : Ch → Yb) (yG : Yb → V) (YQ : Type) (yQ : Yb → YQ),
      (∀ y, ∃! β, ∃ κ : G, κ • yb β = y) ∧ (∀ β (κ : G), κ ∈ H β ↔ κ • yb β = yb β) ∧ (∀ (κ : G) y, yG (κ • y) = κ • yG y) ∧
      (∀ y y', yG y = yG y' → yQ y = yQ y' → y = y') ∧ (∀ (κ : G) y, zQ κ = 1 → yQ (κ • y) = yQ y) := by
  classical
  have hfq : ∀ β q, Finite (Wq q ⧸ Kc β q) := fun β q => by
    haveI := hfi β q
    infer_instance

  let fQ : ∀ β, G ⧸ H β → ∀ q, Wq q ⧸ Kc β q := fun β c =>
    Quotient.liftOn' c (fun g q => ((zQ g q : Wq q) : Wq q ⧸ Kc β q)) (by
      intro a b hab
      have hm := ((hH β (a⁻¹ * b)).mp (QuotientGroup.leftRel_apply.mp hab)).1
      funext q
      apply QuotientGroup.eq.mpr
      simpa [map_mul, map_inv] using hm q)

  let fG : ∀ β, G ⧸ H β → V := fun β c =>
    Quotient.liftOn' c (fun g => g • w β) (by
      intro a b hab
      have hs := ((hH β (a⁻¹ * b)).mp (QuotientGroup.leftRel_apply.mp hab)).2
      rw [mul_smul, inv_smul_eq_iff] at hs
      exact hs.symm)
  have hinj : ∀ (y y' : Σ β, G ⧸ H β), fG y.1 y.2 = fG y'.1 y'.2 →
      (⟨y.1, fQ y.1 y.2⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q) = ⟨y'.1, fQ y'.1 y'.2⟩ → y = y' := by
    rintro ⟨β, c⟩ ⟨β', c'⟩ hG hQ
    obtain rfl : β = β' := congrArg Sigma.fst hQ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective c'
    have hQ' : fQ β g = fQ β g' := eq_of_heq (Sigma.mk.inj hQ).2
    have hG' : g • w β = g' • w β := hG
    have hmem : g⁻¹ * g' ∈ H β := by
      refine (hH β _).mpr ⟨fun q => ?_, ?_⟩
      · have hq : ((zQ g q : Wq q) : Wq q ⧸ Kc β q) = ((zQ g' q : Wq q) : Wq q ⧸ Kc β q) := congrFun hQ' q
        have := QuotientGroup.eq.mp hq
        simpa [map_mul, map_inv] using this
      · rw [mul_smul, ← hG', inv_smul_smul]
    exact congrArg (Sigma.mk β) (QuotientGroup.eq.mpr hmem)
  refine ⟨Σ β, G ⧸ H β,
    Finite.of_injective (fun y => (fG y.1 y.2, (⟨y.1, fQ y.1 y.2⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q)))
      (fun y y' h => hinj y y' (congrArg Prod.fst h) (congrArg Prod.snd h)),
    inferInstance, fun β => ⟨β, ((1 : G) : G ⧸ H β)⟩, fun y => fG y.1 y.2,
    Σ β, ∀ q, Wq q ⧸ Kc β q, fun y => ⟨y.1, fQ y.1 y.2⟩, ?_, ?_, ?_, hinj, ?_⟩
  · rintro ⟨β, c⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨β, ⟨g, ?_⟩, ?_⟩
    · show (⟨β, g • ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (g : G ⧸ H β)⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    · rintro β' ⟨κ, hκ⟩
      exact congrArg Sigma.fst hκ
  · intro β κ
    have e : κ • (⟨β, ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (κ : G ⧸ H β)⟩ := by
      show (⟨β, κ • ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (κ : G ⧸ H β)⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    show κ ∈ H β ↔ κ • (⟨β, ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, ((1 : G) : G ⧸ H β)⟩
    rw [e]
    constructor
    · intro hk
      exact congrArg (Sigma.mk β) (QuotientGroup.eq.mpr (by simpa using hk))
    · intro hk
      have h2 : (κ : G ⧸ H β) = ((1 : G) : G ⧸ H β) := eq_of_heq (Sigma.mk.inj hk).2
      simpa using QuotientGroup.eq.mp h2
  · rintro κ ⟨β, c⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show fG β (κ • (g : G ⧸ H β)) = κ • fG β g
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    exact mul_smul κ g (w β)
  · rintro κ ⟨β, c⟩ hk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show (⟨β, fQ β (κ • (g : G ⧸ H β))⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q) = ⟨β, fQ β g⟩
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    refine congrArg (Sigma.mk β) (funext fun q => ?_)
    show ((zQ (κ * g) q : Wq q) : Wq q ⧸ Kc β q) = ((zQ g q : Wq q) : Wq q ⧸ Kc β q)
    rw [map_mul, hk, one_mul]

end Abs

end GlobalTheory.Mem.Col2.TwistLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExt
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocIntegral

open Polynomial
open scoped WithZero

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem exists_valued_eq (γ : ℤᵐ⁰) : ∃ c : v.adicCompletion K, Valued.v c = γ := by
  obtain ⟨x, hx⟩ := v.valuation_surjective K γ
  exact ⟨algebraMap K _ x, (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans hx⟩

theorem valued_coeff_minpoly_le_one (e : ℕ) (he : 0 < e)
    (f : v.adicCompletion K →+* v'.adicCompletion L)
    (hfv : ∀ y, Valued.v (f y) = Valued.v y ^ e) :
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ x : v'.adicCompletion L, Valued.v x ≤ 1 →
      ∀ n, Valued.v ((minpoly (v.adicCompletion K) x).coeff n) ≤ 1 := by
  letI := f.toAlgebra
  intro hfd x hx n
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ ℤᵐ⁰
  haveI : IsUltrametricDist (v.adicCompletion K) :=
    inferInstanceAs (@IsUltrametricDist (v.adicCompletion K)
      (Valued.toNormedField (v.adicCompletion K) ℤᵐ⁰).toDist)
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  choose c hc using (exists_valued_eq (v := v) : ∀ γ : ℤᵐ⁰, ∃ c : v.adicCompletion K, Valued.v c = γ)
  have hmono : ∀ a b : v.adicCompletion K, Valued.v a ≤ Valued.v b → ‖a‖ ≤ ‖b‖ :=
    fun a b h => Valued.toNormedField.norm_le_iff.2 h
  have hnorm : ∀ a b : v.adicCompletion K, Valued.v a = Valued.v b → ‖a‖ = ‖b‖ :=
    fun a b h => le_antisymm (hmono a b h.le) (hmono b a h.ge)
  have he' : (e : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast he.ne')
  let ρ : v'.adicCompletion L → ℝ := fun z => ‖c (Valued.v z)‖ ^ ((e : ℝ)⁻¹)
  have ρ_nonneg : ∀ z, 0 ≤ ρ z := fun z => Real.rpow_nonneg (norm_nonneg _) _
  have ρ_mul : ∀ a b, ρ (a * b) = ρ a * ρ b := by
    intro a b
    simp only [ρ]
    rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← norm_mul]
    congr 1
    apply hnorm
    rw [hc, Valuation.map_mul, Valuation.map_mul, hc, hc]
  have ρ_le : ∀ a b, Valued.v a ≤ Valued.v b → ρ a ≤ ρ b := by
    intro a b h
    exact Real.rpow_le_rpow (norm_nonneg _) (hmono _ _ (by rw [hc, hc]; exact h))
      (inv_nonneg.2 (Nat.cast_nonneg _))
  have ρ_zero : ρ 0 = 0 := by
    simp only [ρ]
    have : c (Valued.v (0 : v'.adicCompletion L)) = 0 := by
      rw [← Valuation.zero_iff Valued.v, hc, Valuation.map_zero]
    rw [this, norm_zero, Real.zero_rpow he']
  have ρ_eq_zero : ∀ z, ρ z = 0 → z = 0 := by
    intro z hz
    simp only [ρ] at hz
    rw [Real.rpow_eq_zero (norm_nonneg _) he', norm_eq_zero] at hz
    have := hc (Valued.v z)
    rw [hz, Valuation.map_zero] at this
    exact (Valuation.zero_iff _).1 this.symm
  have ρ_f : ∀ a, ρ (f a) = ‖a‖ := by
    intro a
    simp only [ρ]
    rw [hnorm _ (a ^ e) (by rw [hc, hfv, Valuation.map_pow]), norm_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) he.ne']
  have ρ_one : ρ 1 = 1 := by
    have := ρ_f 1
    rwa [map_one, norm_one] at this
  let N : AlgebraNorm (v.adicCompletion K) (v'.adicCompletion L) :=
    { toFun := ρ
      map_zero' := ρ_zero
      add_le' := fun a b => by
        rcases le_total (Valued.v a) (Valued.v b) with h | h
        · have := ρ_le (a + b) b ((Valuation.map_add _ a b).trans (max_le h le_rfl))
          linarith [ρ_nonneg a]
        · have := ρ_le (a + b) a ((Valuation.map_add _ a b).trans (max_le le_rfl h))
          linarith [ρ_nonneg b]
      neg' := fun a => by simp only [ρ, Valuation.map_neg]
      mul_le' := fun a b => (ρ_mul a b).le
      eq_zero_of_map_eq_zero' := ρ_eq_zero
      smul' := fun a z => by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, ρ_mul, ρ_f] }
  have hN : ∀ z, N z = ρ z := fun _ => rfl
  have hpm : IsPowMul N := by
    intro a k hk
    clear hk
    rw [hN, hN]
    induction k with
    | zero => simp [ρ_one]
    | succ k ih => rw [pow_succ, ρ_mul, ih, pow_succ]
  have hu := spectralNorm_unique (K := v.adicCompletion K) (L := v'.adicCompletion L) hpm
  have hsx : spectralNorm (v.adicCompletion K) (v'.adicCompletion L) x ≤ 1 := by
    rw [← spectralAlgNorm_def, ← hu, hN, ← ρ_one]
    exact ρ_le x 1 (by rw [Valuation.map_one]; exact hx)
  have hxi : IsIntegral (v.adicCompletion K) x := Algebra.IsIntegral.isIntegral x
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hxi)] at hsx
  exact Valued.toNormedField.norm_le_one_iff.1 (hsx n)

end GlobalTheory.LocIntegral

namespace GlobalTheory.LocIntegral

open Polynomial

theorem isIntegral_iff_isIntegral_map : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ)
    (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e →
    (∀ y, Valued.v (f y) = Valued.v y ^ e) →
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ b₀ : Kbar v ≃+* Kbar v',
      (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) =
        algebraMap (v'.adicCompletion L) (Kbar v') (f x)) →
      ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔
        IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  intro K L _ _ _ _ v v' e f he hfv
  letI := f.toAlgebra
  intro hfd b₀ hb y
  have hle : ∀ a ∈ v.adicCompletionIntegers K, f a ∈ v'.adicCompletionIntegers L := by
    intro a ha
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hfv]
    exact pow_le_one₀ zero_le' ha
  let g : v.adicCompletionIntegers K →+* v'.adicCompletionIntegers L :=
    f.restrict (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) hle
  have hg : ∀ a, ((g a : v'.adicCompletionIntegers L) : v'.adicCompletion L) = f a := fun _ => rfl
  have hcomp : (algebraMap (v'.adicCompletionIntegers L) (Kbar v')).comp g =
      b₀.toRingHom.comp (algebraMap (v.adicCompletionIntegers K) (Kbar v)) := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v),
      IsScalarTower.algebraMap_apply (v'.adicCompletionIntegers L) (v'.adicCompletion L) (Kbar v'),
      hb]
    rfl
  constructor
  · intro hy
    exact IsIntegral.map_of_comp_eq g b₀.toRingHom hcomp hy
  · intro hy
    letI alg1 : Algebra (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := g.toAlgebra
    letI alg2 : Algebra (v'.adicCompletionIntegers L) (Kbar v) :=
      (b₀.symm.toRingHom.comp (algebraMap (v'.adicCompletionIntegers L) (Kbar v'))).toAlgebra
    haveI : IsScalarTower (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) (Kbar v) := by
      refine IsScalarTower.of_algebraMap_eq fun a => ?_
      have h := congrArg (fun φ => b₀.symm (φ a)) hcomp
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h
      rw [← h]
      rfl
    haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := by
      constructor
      intro a
      have ha : Valued.v (a : v'.adicCompletion L) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2
      have hc := valued_coeff_minpoly_le_one e he f hfv hfd (a : v'.adicCompletion L) ha
      have hai : IsIntegral (v.adicCompletion K) (a : v'.adicCompletion L) :=
        Algebra.IsIntegral.isIntegral _
      have hl : minpoly (v.adicCompletion K) (a : v'.adicCompletion L) ∈
          Polynomial.lifts (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hc n)⟩, rfl⟩
      obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hai)
      refine ⟨q, hm, ?_⟩
      apply Subtype.ext
      have e1 := Polynomial.hom_eval₂ q (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L))
        (v'.adicCompletionIntegers L).subtype a
      have e2 : ((v'.adicCompletionIntegers L).subtype).comp
          (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L)) =
          (algebraMap (v.adicCompletion K) (v'.adicCompletion L)).comp
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        ext; rfl
      rw [e2, ← Polynomial.eval₂_map, hq] at e1
      exact e1.trans (minpoly.aeval (v.adicCompletion K) (a : v'.adicCompletion L))
    have h1 : IsIntegral (v'.adicCompletionIntegers L) y := by
      have := IsIntegral.map_of_comp_eq (RingHom.id (v'.adicCompletionIntegers L)) b₀.symm.toRingHom
        (by ext; rfl) hy
      simpa using this
    exact isIntegral_trans y h1

end GlobalTheory.LocIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurPairingInvariantUnderStandardGroupStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_pairing_invariant_under_standard_group : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurAll D → V.SigOK → IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (h : Formalism.AUTREP.GAf D.host.E n), ∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ipM M μ 𝓕 (principalLevelFrame.actM P M h x) (principalLevelFrame.actM P M h y) = ipM M μ 𝓕 x y := by
  first | exact @GlobalTheory.SchurPairingInvariant.ipM_actM | exact GlobalTheory.SchurPairingInvariant.ipM_actM | (intros; apply GlobalTheory.SchurPairingInvariant.ipM_actM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAdmissibleUnitaryMemSupIsotypicPartsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_admissible_unitary_mem_sup_isotypic_parts : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x})) → (∀ x ∈ C, ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x) → ∀ x ∈ C, x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π := by
  first | exact @GlobalTheory.SpanIsot.span_isotIn | exact GlobalTheory.SpanIsot.span_isotIn | (intros; apply GlobalTheory.SpanIsot.span_isotIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_word_action_continuous : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), Continuous fun g : Formalism.REAL.UJ ε => word (trRep σ P) l (σ (umat g) w) := by
  first | exact @GlobalTheory.SmVec.WordCont.continuous_word_translate | exact GlobalTheory.SmVec.WordCont.continuous_word_translate | (intros; apply GlobalTheory.SmVec.WordCont.continuous_word_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanEigenformsAdelicFormsIffClassPresentationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_eigenforms_adelic_forms_iff_class_presentation : ∀ {G Γ W K G0 : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) [Group G0] [Fintype G0] (Q : Subgroup G) (ch : Q →* ℂˣ) (act : Representation K G0 S.Forms) (P : Bridge.ClassPres ι S σ ρ J χ) (Tt : Bridge.ActTie ι P Q ch act), P.ExtBij → ∀ (U : Subgroup G0) (ψ : U →* Kˣ) (Φ : G → W), Φ ∈ Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ↔ (Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G), Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h) := by
  first | exact @GlobalTheory.LiftSpanEig.eigen_span_iff | exact GlobalTheory.LiftSpanEig.eigen_span_iff | (intros; apply GlobalTheory.LiftSpanEig.eigen_span_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassEquivReferenceTupleEqSelfStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eCls0_mu0_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (c : (I.stp u I.mu0 0).Cl), I.eCls0 l u I.mu0 c = c := by
  first | exact @GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self | exact GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self | (intros; apply GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDefStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroColumns_classSumForm_posDef : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), SpectralModel.ColsPos (I.cols l) := by
  first | exact @GlobalTheory.Mem.Df.cols_pos | exact GlobalTheory.Mem.Df.cols_pos | (intros; apply GlobalTheory.Mem.Df.cols_pos <;> assumption)
end

