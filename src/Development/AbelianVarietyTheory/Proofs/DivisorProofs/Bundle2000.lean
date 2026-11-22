import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelReductionHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeTateLevel

open GlobalTheory.KernelNoTorsion GlobalTheory.TangentPow GlobalTheory.TorsionCharacter GlobalTheory.HTLat.OmegaRank GlobalTheory.GmPoints
open GlobalTheory.CompHt.FormalChar GlobalTheory.RaynaudTorsionMap GlobalTheory.HodgeTateImage

theorem exists_lift_of_nilpotent {O : Type} [CommRing O] {H Y : Over (Sp O)} (j : H ⟶ Y) [IsOpenImmersion j.left]
    {R : Type} [CommRing R] [Algebra O R] (I : Ideal R) (hI : IsNilpotent I) (g : specO O R ⟶ Y)
    (z : specO O (R ⧸ I) ⟶ H) (hz : z ≫ j = ptMap (Ideal.Quotient.mkₐ O I) ≫ g) :
    ∃ w : specO O R ⟶ H, w ≫ j = g := by
  have hr : Set.range g.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      obtain ⟨k, hk⟩ := hI
      intro a ha
      refine y.isPrime.mem_of_pow_mem k ?_
      have h0 : a ^ k ∈ I ^ k := Ideal.pow_mem_pow ha k
      rw [hk] at h0
      rw [show a ^ k = 0 from h0]
      exact Ideal.zero_mem _
    obtain ⟨y', rfl⟩ := hy
    exact ⟨z.left y', congrArg (fun q => q.left y') hz⟩
  refine ⟨Over.homMk (IsOpenImmersion.lift j.left g.left hr) ?_,
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]

theorem hom_ext_open {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G] {N : ℕ} {H T : Over (Sp O)}
    (j : H ⟶ torsion G N) [IsOpenImmersion j.left] {w w' : T ⟶ H}
    (h : w ≫ j ≫ torsion.ι G N = w' ≫ j ≫ torsion.ι G N) : w = w' := by
  have e : w ≫ j = w' ≫ j := torsion_hom_ext (by rw [Category.assoc, Category.assoc, h])
  refine Over.OverMorphism.ext ?_
  rw [← cancel_mono j.left]
  exact congrArg (·.left) e

theorem exists_lift_near_unit {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G] {N : ℕ} {H : Over (Sp O)}
    {j : H ⟶ torsion G N} (hj : IsOpenFiniteFlatSubgroup G N j) {R : Type} [CommRing R] [Algebra O R]
    (I : Ideal R) (hI : IsNilpotent I) (g : specO O R ⟶ G) (hg : g ^ N = 1)
    (h1 : ptMap (Ideal.Quotient.mkₐ O I) ≫ g = 1) : ∃ w : specO O R ⟶ H, w ≫ j ≫ torsion.ι G N = g := by
  haveI := hj.1
  obtain ⟨z, hz⟩ := hj.2.2.2.1 (specO O (R ⧸ I))
  obtain ⟨w, hw⟩ := exists_lift_of_nilpotent j I hI (torsionLift g hg) z (torsion_hom_ext (by
    rw [Category.assoc, Category.assoc, hz, torsionLift_ι, h1]))
  exact ⟨w, by rw [← Category.assoc, hw, torsionLift_ι]⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem exists_corr {N : ℕ} {H : Over (Sp O)} {j : H ⟶ torsion P.G N} (hj : IsOpenFiniteFlatSubgroup P.G N j)
    {A : Type} [CommRing A] [Algebra O A] (hc : IsAdicComplete (Ideal.span {(p : A)}) A) (I : Ideal A) {k : ℕ}
    (hI : I ^ k ≤ Ideal.span {(p : A)}) (x : specO O A ⟶ P.Gt) (hx : x ^ N = 1)
    (h1 : ptMap (Ideal.Quotient.mkₐ O I) ≫ x = 1) :
    ∃ Q : specO O A ⟶ H, Corr P x (Q ≫ j ≫ torsion.ι P.G N) := by
  haveI := P.isLocalRing
  haveI := hj.1
  haveI := hj.2.1
  haveI := hj.2.2.1
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := exists_finite_free H
  have ex : ∀ m : ℕ, ∃ w : specO O (A ⧸ Ideal.span {(p : A) ^ m}) ⟶ H,
      w ≫ j ≫ torsion.ι P.G N = P.cmp _ (nilpR m) (ptMap (redR p O A m) ≫ x) := fun m => by
    let θ := redR p O A m
    refine exists_lift_near_unit hj (I.map θ) ⟨k * m, eq_bot_iff.2 ?_⟩ _ ?_ ?_
    · rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap, pow_mul]
      refine (Ideal.pow_right_mono hI _).trans fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ?_
      rwa [Ideal.span_singleton_pow] at ha
    · rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]
    · have h' : IsNilpotent (p : (A ⧸ Ideal.span {(p : A) ^ m}) ⧸ I.map θ) := by
        simpa using (nilpR (p := p) (R := A) m).map (Ideal.Quotient.mk (I.map θ))
      have e1 : (Ideal.Quotient.mkₐ O (I.map θ)).comp θ =
          (Ideal.quotientMapₐ (I.map θ) θ Ideal.le_comap_map).comp (Ideal.Quotient.mkₐ O I) := rfl
      rw [← P.cmp_nat _ _ (nilpR m) h', ← Category.assoc, ptMap_comp_ptMap, e1, ← ptMap_comp_ptMap, Category.assoc, h1,
        MonObj.comp_one, map_one]
  choose w hw using ex
  obtain ⟨Q, hQ⟩ := exists_lim_affine hc (fun m => w m ≫ e.inv) fun m => by
    rw [← Category.assoc]
    congr 1
    apply hom_ext_open j
    rw [Category.assoc, hw, hw, ← P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), ← Category.assoc, factor_redR]
  refine ⟨Q ≫ e.hom, fun m => ?_⟩
  rw [Category.assoc, ← Category.assoc, hQ, Category.assoc, Iso.inv_hom_id_assoc, hw]

theorem weil_mul_swap [IsAlgClosed C] [CharZero C] {A : Out.PolAV (Sp C)} {k : ℕ} (hk : 1 ≤ k) {z s : ChTor.Pts A.A}
    (hz : z ^ k = 1) (hs : s ^ k = 1) : weil A k z s * weil A k s z = 1 := by
  have hzs : (z * s) ^ k = 1 := by rw [mul_pow, hz, hs, _root_.mul_one]
  have h := weil_self hk hzs
  rwa [weil_mul_left hk hz hs hzs, weil_mul_right hk hz hs hz, weil_mul_right hk hz hs hs, weil_self hk hz,
    weil_self hk hs, _root_.one_mul, _root_.mul_one] at h

theorem levelReduction : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), LevelReduction P := by
  intro p hp C _ _ _ v O _ _ _ hO _ _ _ Λ _ _ P n H j hj t χ _ hχ R _ _ hR x w hw
  have hv := P.integers
  have hp0 := hp.out.ne_zero
  have hN := one_le_ppow p n
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI := ValuationRing.of_integers v hv
  haveI := (P.finite_flat _ hN).1
  haveI := (P.finite_flat _ hN).2
  haveI := hj.1
  obtain ⟨A, _, _, X, I, m, _, _, hsep, hX, hI, hl⟩ := exists_connected_part hv hp0 P.Gt (p ^ n) (pow_ne_zero n hp0)
  have hAc : IsAdicComplete (Ideal.span {(p : A)}) A := by
    have := FlatComplete.isAdicComplete_of_finite_flat _ _ hO A
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  obtain ⟨Q, hQ⟩ := exists_corr P hj hAc I hI (X ≫ torsion.ι P.Gt (p ^ n))
    (by rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]) hX
  have e : (unitOf (Q ≫ χ) : A) * (unitOf (X ≫ (P.weilChar t).χ n) : A) = 1 := hsep _ _ fun φ => hv.hom_inj (by
    have h1 : P.toG ((ptMap φ ≫ X) ≫ torsion.ι P.Gt (p ^ n)) = (ptMap φ ≫ Q) ≫ j ≫ torsion.ι P.G (p ^ n) :=
      P.hom_ext_red fun k => by
        rw [P.red_toG, Category.assoc (ptMap φ), Category.assoc (ptMap φ)]
        exact (hQ.comp φ k).symm
    have h2 := hχ (ptMap φ ≫ Q) _ (h1 ▸ (P.eq_toA_iff _ _).1 rfl)
    rw [map_mul, map_mul, ← unitOf_ptMap, ← unitOf_ptMap, ← Category.assoc, ← Category.assoc, h2,
      P.isWeilChar_weilChar, ← Units.val_mul, weil_mul_swap hN (t.lev_pow n) (P.toA_pow _), map_one, map_one,
      Units.val_one])
  have hn := isNilpotent_dual hR
  have hpow : (ptMap (dualBC (Algebra.ofId O R)) ≫ x.1) ^ p ^ n = 1 := (P.cmp _ hn).injective (by
    rw [map_pow, ← hw, map_one, ← MonObj.comp_pow, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, MonObj.comp_one])
  obtain ⟨ψ, hψ⟩ := hl R (torsionLift _ hpow) (by rw [torsionLift_ι]; exact fst_bc R x)
  have hx : (ptMap ψ ≫ X) ≫ torsion.ι P.Gt (p ^ n) = ptMap (dualBC (Algebra.ofId O R)) ≫ x.1 := by
    rw [← hψ, torsionLift_ι]
  have hw' : w = ptMap ψ ≫ Q := hom_ext_open j (by
    rw [hw, ← hx, Category.assoc, cmp_of_corr P hQ, Category.assoc])
  have h3 := isAl_dlogTv (P.weilChar t) n R hR x _ hx
  have h4 := congrArg ψ e
  rw [map_mul, map_one, ← unitOf_ptMap, ← unitOf_ptMap, ← Category.assoc, ← Category.assoc, ← hw', h3] at h4
  have h5 : algebraMap O R ((alLeft P t).1 x) = -algebraMap O R ((dlogTv (P.weilChar t)).1 x) := by
    rw [← map_neg]
    rfl
  rw [h5]
  generalize algebraMap O R ((dlogTv (P.weilChar t)).1 x) = a at h4 ⊢
  have h6 : (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr a : DualNumber R) *
      (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (-a)) = 1 := by
    ext <;> simp
  rw [← _root_.mul_one (unitOf (w ≫ χ) : DualNumber R), ← h6, ← _root_.mul_assoc, h4, _root_.one_mul]

end GlobalTheory.HodgeTateLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertAvg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tens_inj (v : Pl F) {κ : Type} (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRt : ∀ x z, At (evFin F v) z → R (x + z) = R x) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (e : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hRt 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

theorem acts_unique (v : Pl F) {κ : Type} [Fintype κ] (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  exact tens_inj v R hR0 (hR φ hφ).1 ((h₁ R (hR φ hφ)).symm.trans (h₂ R (hR φ hφ)))

section Grp
variable {n : ℕ} {W : Spc F E n}

theorem mat_mul (g h : UA σ W.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul (h : UA σ W.J) : mat h⁻¹ * mat h = 1 := by
  rw [← mat_mul, inv_mul_cancel]; rfl

theorem mat_one : mat (1 : UA σ W.J) = 1 := rfl

theorem uAt_mul (v : Pl F) {g h : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) (hh : h ∈ UAt σ W (evFin F v)) :
    g * h ∈ UAt σ W (evFin F v) := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    rw [mat_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  show u • (mat (g * h) - 1) = 0
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem uAt_inv (v : Pl F) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) : h⁻¹ ∈ UAt σ W (evFin F v) := by
  intro u hu
  have e : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by
    rw [Matrix.mul_sub, mat_inv_mul, Matrix.mul_one]; abel
  show u • (mat h⁻¹ - 1) = 0
  rw [e, smul_neg, ← Matrix.mul_smul, hh u hu, Matrix.mul_zero, neg_zero]

end Grp

section Loc
variable {a a' : ℕ} {B : Base F E} (G : Geo σ a a') {X : Chars F E}

open Classical in

def loc (om : Rep σ G.V G.W) (v : Pl F) (h : UA σ G.W.J) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) :
    (Fin a × Fin (a + a') → Fv F v) → ℂ :=
  if hx : ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ then hx.choose else 0

variable {G} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem tens_add (v : Pl F) {κ : Type} (φ ψ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ) :
    tens (evFin F v) (φ + ψ) r = tens (evFin F v) φ r + tens (evFin F v) ψ r := by
  funext x; simp [tens, add_mul]

end Loc

end GlobalTheory.InertAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalProductFormula
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolCompact

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf' {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem locFin_second (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

theorem exists_sa_of_mem_kInf (hP : GlobalTheory.FunPr.Hypotheses₂) {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hb : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hw : M.IsWeil B.ψ χX χW om) {k : UA σ W.J}
    (hk : k ∈ KInf σ W B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ f₁ ∈ M.Pol B.ψ B.emb, SA (om (1, k)) f f₁ := by
  have hfr : GlobalTheory.RealLift.FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : GlobalTheory.RealLift.DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : GlobalTheory.RealLift.FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hls : GlobalTheory.RealLift.LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder hvl
  have hpr : GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.T.archActionReadings_compatible hder hvl
  have hkl : GlobalTheory.RealLift.KLine := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.T.unitaryLieElements_generate_oneParamLines
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf']; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hw
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ hwp.1.1
  have hadm := fun g => (hwp.isUSplitting).adm g
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
    hkl F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C W.θ hb.cm hC1 hCθ k hk.1 hk.2
  have hloc := GlobalTheory.RealLift.locFin_sumPl _ _ _ (fun w => locFin_second r s r' s' (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, -, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  rw [← hr] at hf ⊢
  obtain ⟨T, rfl⟩ := hf
  refine ⟨Φ (U T), LinearMap.mem_range_self Φ _, ?_⟩
  have h1 := hSA T
  rw [MonoidHom.comp_apply, hγ1] at h1
  exact h1

theorem polData_stable_kInf (hP : GlobalTheory.FunPr.Hypotheses₂) {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hb : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ) (hw : M.IsWeil B.ψ χX χW om) {k : UA σ W.J}
    (hk : k ∈ KInf σ W B.emb) {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) : om (1, k) Φ ∈ PolData B M := by
  have hle : PolData B M ≤ (PolData B M).comap (om (1, k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, φ, hSB, hev, rfl⟩
    obtain ⟨f₁, hf₁, hsa⟩ := exists_sa_of_mem_kInf hP hb hX hW hw hk hf
    have hg := GlobalTheory.AdelicCoordSB.finprod_mem_SB F (Fin n × Fin d) φ hSB
      ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)
    have e : om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ := hsa _ hg
    change om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ PolData B M
    rw [e]
    exact Submodule.subset_span ⟨f₁, hf₁, φ, hSB, hev, rfl⟩
  exact hle hΦ

theorem polData_small_stable_kInf : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ k ∈ KInf σ G.W B.emb, ∀ Φ ∈ PolData B G.M', om' (1, k) Φ ∈ PolData B G.M' := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf h k hk Φ hΦ
  exact polData_stable_kInf hK.base h.triple.base h.triple.geo.hV' h.triple.geo.hW h.triple.geo.hM' h.triple.weil' hk hΦ

end GlobalTheory.PolCompact

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactArchOperatorPreservesFockVacua
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KInfVac

open GlobalTheory.RealLift GlobalTheory.KInfPol

theorem gaussD_of_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ g : SInf F (Fin n × Fin d), GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb g → GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb (A g) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk A hA f₀ hf₀
  have hB := hP.base
  have hw := hP.weil
  rw [← GlobalTheory.ThK.EvAt0.PolEv.isGauss_iff hB.std] at hf₀ ⊢
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  obtain ⟨ε, hε⟩ := hf₀
  refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
  have hv := at_mul_right hu (mat k⁻¹)ᵀ
  have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
  have h1 := hint _ hv f₀
  have h2 := hint _ hv' f₀
  rw [hcan] at h1 h2
  have e1 := (hL _ _ _).2.2.1 _ hg h1
  have e2 := (hL _ _ _).2.2.1 _ hg' h2
  have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
  · rw [e1, e2, key, map_smul]
  · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
      rw [← Matrix.map_mul]
      change (mat (k⁻¹ * k)).map _ = 1
      rw [inv_mul_cancel]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
    have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
      calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
            ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
        _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
            (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
    rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]

end GlobalTheory.KInfVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReadsStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ (c : ℂ) (f₀ : WO S T → ℂ), Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∀ f, Reads ψ θ hS hT cc δ r G f → Reads ψ θ hS hT cc δ r (c • W.Om x y G) (om (g, h) f) := by
  first | exact @GlobalTheory.NormExact.reads_om_of_vacuum | exact GlobalTheory.NormExact.reads_om_of_vacuum | (intros; apply GlobalTheory.NormExact.reads_om_of_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialOfIsSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TypeTwo.PowIrrProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem equiv_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
    (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨y, hy⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf y
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  rcases eq_bot_or_eq_top S with rfl | rfl
  · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
  let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
  have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
  refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  rcases eq_bot_or_eq_top F.ker with h | h
  · have : x ∈ F.ker := hx
    rw [h] at this
    exact this
  · have : v.1 ∈ F.ker := by rw [h]; trivial
    exact absurd this hy

theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W] :
    Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  have := hf.nontrivial
  exact Subtype.val_injective.nontrivial (α := S.toSubmodule)

end GlobalTheory.TypeTwo.PowIrrProof

namespace GlobalTheory.TypeTwo.PowIrrProof

end GlobalTheory.TypeTwo.PowIrrProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovolStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (k : ℕ), LocallyCompactSpace ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ SecondCountableTopology ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ DiscreteTopology ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) ∧ ∀ [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (π : Measure ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) (DM : Set ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker), π.IsHaarMeasure → IsFundamentalDomain ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.GLOneVol.glOne_finvol | exact GlobalTheory.GLOneVol.glOne_finvol | (intros; apply GlobalTheory.GLOneVol.glOne_finvol <;> assumption)
end

