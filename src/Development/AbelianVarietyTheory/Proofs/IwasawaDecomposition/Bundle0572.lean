import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.FrCovA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocM.FrameBC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X}

theorem tv_sum' {κ : Type} (s : Finset κ) (f : κ → TanM x t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  simp only [tv, toMul_sum, Subgroup.val_finset_prod]

def Full {κ : Type} [Fintype κ] (v : κ → TanM x t.G) : Prop :=
  ∀ n : TanM x t.G, ∃! a : κ → S, n = ∑ k, a k • v k

theorem full_equiv {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ' ≃ κ) {v : κ → TanM x t.G} (hv : Full v) :
    Full (fun i => v (e i)) := fun n => by
  obtain ⟨a, ha, hu⟩ := hv n
  refine ⟨fun i => a (e i), ha.trans (e.sum_comp (fun k => a k • v k)).symm, fun b hb => ?_⟩
  have := hu (fun k => b (e.symm k)) (hb.trans (by
    rw [← e.sum_comp]; simp only [Equiv.symm_apply_apply]))
  funext i; rw [← this]; simp

theorem full_iff {m : ℕ} {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → TanM x t.G}
    (e : ∀ i, pushHom h (epsR S) (u i) = tv (v i)) : IsLieBasis u ↔ Full v := by
  have key : ∀ a p n, pushHom h (epsR S) p = tv n → (IsLieComb a u p ↔ n = ∑ k, a k • v k) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    exact ⟨fun q => tanM_ext (q.trans (by rw [tv_sum']; rfl)), fun q => (congrArg tv q).trans (by rw [tv_sum']; rfl)⟩
  refine ⟨fun hu n => ?_, fun hv => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv n)
    simpa only [key _ p n hp] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem n))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using hv (mkT _ ((isTangent_iff h p).1 hp))

def resM (ψ : S →+* T) (n : TanM x t.G) : TanM (spMap ψ ≫ x) t.G := tanOf (isTan_map ψ rfl (isTan_tv n))

theorem full_bc {m : ℕ} (ψ : S →+* T) {v : Fin m → TanM x t.G} (hv : Full v) : Full fun i => resM ψ (v i) := by
  have h₀ := isGrpPullback_pullback t.G x
  have h := isGrpPullback_pullback t.G (spMap ψ ≫ x)
  choose u hu using fun i => push_surj h₀ (tv (v i))
  choose u' hu' using fun i => push_surj h (tv (resM ψ (v i)))
  have := t.semi.smooth
  have : Smooth ((Over.pullback x).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (full_iff h hu').1 (Chart.frameLieBCR _ ((full_iff h₀ hu).2 hv) ψ (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (PullbackSections.dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

variable {l : Level H} (c : Coeff l) [Algebra c.F S]

theorem eig_iff (τ : E →+* ℂ) (n : TanM x t.G) :
    (∀ a : 𝓞 E, (tv n).left ≫ (t.act.act a).left = spMap (epsMul (algebraMap c.F S (embK c τ a))) ≫ (tv n).left) ↔
      IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n :=
  forall_congr' fun _ => ⟨fun h => tan_ext h, fun h => congrArg (fun V => (tv V).left) h⟩

theorem eig_comb' (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v i)) (a : Fin m → S) :
    IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hv i b, smul_comm]

theorem full_of_eig {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hv : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hb : ∀ τ n, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n → ∃! a : Fin (d τ) → S, n = ∑ i, a i • v τ i) :
    Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2) := by
  classical
  intro m
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End S (TanM x t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => hb τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), a k.1 k.2 • v k.1 k.2
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), b k • v k.1 k.2 := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • v τ i)
      (fun τ => eig_comb' c τ _ (fun i => hv τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

theorem eig_of_full {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hE : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hfull : Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2)) (τ : E →+* ℂ) (w : TanM x t.G)
    (hm : IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) w) : ∃! a : Fin (d τ) → S, w = ∑ i, a i • v τ i := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hproj : proj ρ (embK c) α τ w = w := by
    have := proj_sum_eig ρ (embK c) α hinj (fun σ' => if σ' = τ then w else 0)
      (fun σ' => by
        split_ifs with h
        · subst h; exact hm
        · exact fun a => by simp) τ
    simpa [Finset.sum_ite_eq'] using this
  obtain ⟨A, hA, hAu⟩ := hfull w
  have hcomp : proj ρ (embK c) α τ w = ∑ i, A ⟨τ, i⟩ • v τ i := by
    have h1 := proj_sum_eig ρ (embK c) α hinj (fun σ' => ∑ i, A ⟨σ', i⟩ • v σ' i)
      (fun σ' => eig_comb' c σ' _ (fun i => hE σ' i) _) τ
    rw [← Fintype.sum_sigma (fun k : (Σ σ : E →+* ℂ, Fin (d σ)) => A k • v k.1 k.2), ← hA] at h1
    exact h1
  refine ⟨fun i => A ⟨τ, i⟩, hproj.symm.trans hcomp, fun b hb => ?_⟩
  have hb : w = ∑ i, b i • v τ i := hb
  let B : (Σ σ : E →+* ℂ, Fin (d σ)) → S := fun k => if h : k.1 = τ then b (h ▸ k.2) else 0
  have hB : w = ∑ k, B k • v k.1 k.2 := by
    rw [Fintype.sum_sigma, hb, Finset.sum_eq_single τ]
    · exact Finset.sum_congr rfl fun i _ => by simp [B]
    · intro σ _ hσ
      exact Finset.sum_eq_zero fun i _ => by simp [B, hσ]
    · intro h; exact absurd (Finset.mem_univ τ) h
  have := hAu B hB
  funext i
  have := congrFun this ⟨τ, i⟩
  simpa [B] using this

end GlobalTheory.LocM.FrameBC

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM.FrameBC in

theorem GlobalTheory.LocM.isFrame_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  intro E _ _ _ H Dw l c X t R S _ _ f φ x u hu
  letI : Algebra c.F R := f.toAlgebra
  letI : Algebra c.F S := (φ.comp f).toAlgebra
  let v : ∀ τ, Fin (Dw.mult τ) → TanM x t.G := fun τ i => tanOf (hu.1 τ i).1
  have he : ∀ τ i (a : 𝓞 E), u.bc φ τ i ≫ (t.act.act a).left =
      spMap (epsMul ((φ.comp f) (embK c τ a))) ≫ u.bc φ τ i := fun τ i a => by
    show (spMap (dualMap φ) ≫ u τ i) ≫ _ = _ ≫ spMap (dualMap φ) ≫ u τ i
    rw [Category.assoc, (hu.1 τ i).2 a, ← Category.assoc, Formalism.L2.Pj.FrCov.eps_dual, Category.assoc, RingHom.comp_apply]
  have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (hu.1 τ i).2) fun τ n hn => by
    exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (hu.2 τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
  have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM φ (v k.1 k.2) := by
    have h := full_equiv (eB Dw).symm (full_bc φ (full_equiv (eB Dw) h1))
    exact (funext fun k => congrArg (fun j : IxB Dw => resM φ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
  refine ⟨fun τ i => ⟨isTan_map φ rfl (hu.1 τ i).1, he τ i⟩, fun τ w hw hwe => ?_⟩
  have h3 := eig_of_full c (fun τ i => resM φ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
    ((eig_iff c τ _).1 hwe)
  exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM φ (v τ i)) a (tanOf hw)).2 h3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorBlockDecomposition
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem lminor_block : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ H : Matrix (Fin r) (Fin r) ℂ, IsUnit (reindex e e H).toBlocks₂₂.det → (∀ (i : Fin (r + 1)) (k : Fin (q + 1)), (i : ℕ) = k → lminor H i = lminor (reindex e e H).toBlocks₂₂ k) ∧ ∀ (i : Fin (r + 1)) (k : Fin (p + 1)), (i : ℕ) = q + k → lminor H i = (reindex e e H).toBlocks₂₂.det * lminor (schur (reindex e e H)) k := by
  intro r p q e he H hH
  constructor
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = k := h
    unfold lminor
    congr 1
    ext a b
    simp only [submatrix_apply, toBlocks₂₂, reindex_apply, of_apply]
    congr 1 <;> exact Fin.ext (by rw [he.2]; rfl)
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = q + k := h
    obtain ⟨f0, hf0⟩ := exists_isBlockOrderedSumEquiv k q
    let f : Fin (q + k) ≃ Fin k ⊕ Fin q := (finCongr (add_comm q k)).trans f0
    have hf : IsBlockSL2Embedding f := ⟨fun a => hf0.1 a, fun a => hf0.2 a⟩
    let c : Fin k → Fin p := Fin.castLE (Nat.le_of_lt_succ hk)
    let G : Matrix (Fin k ⊕ Fin q) (Fin k ⊕ Fin q) ℂ := (reindex e e H).submatrix (Sum.map c id) (Sum.map c id)
    have key : ∀ a, Fin.castLE (Nat.le_of_lt_succ hi) (f.symm a) = e.symm (Sum.map c id a) := by
      rintro (a | a) <;> apply Fin.ext
      · simp only [Fin.val_castLE, Sum.map_inl, hf.1, he.1, c]
      · simp only [Fin.val_castLE, Sum.map_inr, hf.2, he.2, id]
    have h1 : lminor H ⟨q + k, hi⟩ = G.det := by
      unfold lminor
      rw [← det_submatrix_equiv_self f.symm]
      congr 1
      ext a b
      simp only [G, submatrix_apply, reindex_apply, ← key]
    have h2 : G.toBlocks₂₂ = (reindex e e H).toBlocks₂₂ := rfl
    rw [h1, det_eq_mul_schur (h2 ▸ hH), h2]
    rfl

end GlobalTheory.FlagFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReadingRationalAtTwistExtendsIntegralUnitarStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelReading_rationalAtTwist_extends_integralUnitary : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n : ℕ} [NeZero n] {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {J : Matrix (Fin n) (Fin n) E}, J = 1 →
    ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ),
    (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → (∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P') →
    (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F);
      ∀ᶠ (u : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) →
    RdLevOn hc (RatAt Q) S.U S.chi Λ emb Q HQ lamQ →
    RdLevOn hc Set.univ S.U S.chi Λ emb Q HQ lamQ := by
  first | exact @GlobalTheory.SeeSaw.TwLev.Approx.rd_all | exact GlobalTheory.SeeSaw.TwLev.Approx.rd_all | (intros; apply GlobalTheory.SeeSaw.TwLev.Approx.rd_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CuspFieldChange

open GlobalTheory.FieldBC GlobalTheory.SecFieldChange
open GlobalTheory.CoefChangeCompare (ValueWD HasBC hasBC_of evR_of_map)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

variable {c c₀ : Coeff l} (hle : c₀.F ≤ c.F)

theorem eq_sum_of_isBC {m : ℕ} {f' : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf' : f' ∈ sec Xo c a n)
    {as : Fin m → c.F} {fs : Fin m → Rul Xo c₀} (h : IsBC hle f' as fs) : f' = ∑ i, as i • rulBC hle (fs i) := by
  funext q y
  letI := resAlg hle q.R
  rw [val_of_isBC hle hf'.1 h q (fun _ => rfl) y, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def]
  rfl

theorem cusp_unfBC_eq_span {r : ℕ} (U : ∀ σ : c₀.F →+* ℂ, Unf Xo c₀ σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (unfBC hle U) a n = Submodule.span c.F (rulBC hle '' (cusp Xo c₀ U a n : Set (Rul Xo c₀))) := by
  refine le_antisymm (fun f' hf' => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, as, fs, hfs, h⟩ := cuspBC_holds hle U a n f' hf'
    rw [eq_sum_of_isBC hle (cusp_le_sec _ _ _ _ _ hf') h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hfs i, rfl⟩)
  · rintro _ ⟨f, hf, rfl⟩
    exact (rulBC_cusp E H Dw l Xo c₀ c hle r U a n f (cusp_le_sec _ _ _ _ _ hf)).2.2 hf

theorem linearIndependent_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {v : Fin m → Rul Xo c₀}
    (hv : ∀ i, v i ∈ sec Xo c₀ a n) (hi : LinearIndependent c₀.F v) :
    LinearIndependent c.F (fun i => rulBC hle (v i)) := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c₀ :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c₀))
  have hBC : HasBC Xo c₀ := hasBC_of hS
  letI alg : Algebra c₀.F c.F := (incF c₀ c hle).toAlgebra
  rw [Fintype.linearIndependent_iff] at hi ⊢
  intro g hg i
  refine (Module.forall_dual_apply_eq_zero_iff c₀.F (g i)).1 fun lam => ?_
  refine hi (fun j => lam (g j)) ?_ i
  funext p y
  have hov : AlgOver c₀ c hle (Ext c₀.F c.F p.R) := fun x => ext_tower x
  obtain ⟨z, hz⟩ := hBC p.R (Ext c₀.F c.F p.R) (inR c.F p.R) y
  have h1 := evR_sum_smul (z.ext hle hov) g (fun i => rulBC hle (v i))
  have h0 : evR Xo c (0 : Rul Xo c) (z.ext hle hov) = 0 := evalAt_zero _ _ _
  rw [hg, h0] at h1
  have h2 : ∀ j, evR Xo c (rulBC hle (v j)) (z.ext hle hov) = inR c.F p.R (v j p y) := fun j => by
    rw [((rulBC_sec_val_linear E H Dw l Xo c₀ c hle).1 a n _ (hv j)).2 _ hov, FrPt.res_ext,
      evR_of_map hWD (hv j).1 hz]
  simp only [h2] at h1
  have h3 : ∀ j, algebraMap c.F (Ext c₀.F c.F p.R) (g j) * inR c.F p.R (v j p y) =
      (TensorProduct.tmul c₀.F (g j) (v j p y) : TensorProduct c₀.F c.F p.R) := fun j => by
    show (TensorProduct.tmul c₀.F (g j) (1 : p.R) * TensorProduct.tmul c₀.F (1 : c.F) (v j p y) :
      TensorProduct c₀.F c.F p.R) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h4 : (0 : TensorProduct c₀.F c.F p.R) = ∑ j, TensorProduct.tmul c₀.F (g j) (v j p y) :=
    h1.trans (Finset.sum_congr rfl fun j _ => h3 j)
  have h5 := congrArg (coord lam p.R) h4
  rw [map_zero, map_sum] at h5
  simp only [coord_tmul] at h5
  rw [Finset.sum_apply, Finset.sum_apply]
  exact h5.symm

end GlobalTheory.CuspFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreserving
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.ProdFibre

theorem lintegral_pi_fibre : ∀ (T A B C : Type) [Fintype T] [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)] [SigmaFinite (volume : Measure C)] (g : A × B → C) (π : C → A) (D : C → ℝ≥0∞) (φ : (T → A) → ℝ≥0∞), MeasurePreserving g volume volume → Measurable π → (∀ w, π (g w) = w.1) → Measurable D → Measurable φ → ∫⁻ c : T → C, φ (fun t => π (c t)) * ∏ t, D (c t) = ∫⁻ a : T → A, φ a * ∏ t, ∫⁻ b, D (g (a t, b)) := by
  intro T A B C _ _ _ _ _ _ _ g π D φ hg hπ hgπ hD hφ
  have h1 : MeasurePreserving (fun (a : T → A × B) (t : T) => g (a t)) volume volume :=
    volume_preserving_pi (f := fun _ : T => g) (fun _ => hg)
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow A B T).symm
  have h3 := h1.comp h2
  have hF : Measurable (fun c : T → C => φ (fun t => π (c t)) * ∏ t, D (c t)) := by
    refine Measurable.mul (hφ.comp ?_) ?_
    · exact measurable_pi_lambda _ (fun t => hπ.comp (measurable_pi_apply t))
    · exact Finset.measurable_prod _ (fun t _ => hD.comp (measurable_pi_apply t))
  rw [← h3.lintegral_comp hF, Measure.volume_eq_prod]
  refine (lintegral_prod _ (hF.comp h3.measurable).aemeasurable).trans ?_
  refine lintegral_congr (fun a => ?_)
  have hm : ∀ t, Measurable (fun b : B => D (g (a t, b))) := fun t =>
    hD.comp (hg.measurable.comp measurable_prodMk_left)
  have hin := GlobalTheory.SnMass.Push.lintegral_fintype_prod (X := fun _ : T => B)
    (μ := fun _ => (volume : Measure B)) (fun t b => D (g (a t, b))) hm
  rw [← hin, ← volume_pi, ← lintegral_const_mul]
  · refine lintegral_congr (fun b => ?_)
    change φ (fun t => π (g (a t, b t))) * ∏ t, D (g (a t, b t)) = _
    simp only [hgπ]
  · exact Finset.measurable_prod _ (fun t _ => (hm t).comp (measurable_pi_apply t))

end GlobalTheory.ProdFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinates
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem measurePreserving_coords_sorted (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ) :
    MeasurePreserving (coords X κ) volume volume := by
  let e : Fin (nd X) ≃ Tau × Low r :=
    ((Equiv.prodCongr κ (Equiv.refl (Low r))).trans (Fintype.equivFin (Ent X))).symm
  have h1 := GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))
  have h2 := volume_preserving_arrowCongr' e (MeasurableEquiv.refl ℂ) (MeasurePreserving.id _)
  have h3 := GlobalTheory.FlagBase.PoissonV.measurePreserving_curry Tau (Low r)
  exact h3.comp (h2.comp h1)

end GlobalTheory.FlagFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicityDifferentEq
section
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad

theorem multiplicity_different_eq (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (p : 𝓞 E) ∈ w.asIdeal) :
    (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) : ℝ) = (eWL E w : ℝ) * vDiff E p := by
  classical
  haveI := Fact.mk hp
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  obtain ⟨a, m, hm, hdisc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd p hp.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E p a m hp hm hdisc w.asIdeal w.isPrime hw
  haveI := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span E p hp w.isPrime hw
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have he : eWL E w = (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count w.asIdeal := by
    rw [eWL, Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(p : ℤ)}) w.asIdeal
      (by rw [hmap]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.span_nat_ne_bot p), hmap]
  have hv : padicValNat p (discr E).natAbs = a := by
    rw [hdisc, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  rw [multiplicity_eq_count_normalizedFactors w.irreducible hD0, normalize_eq, he, vDiff, hv, ← mul_div_assoc,
    eq_div_iff hE, mul_comm _ (a : ℝ)]
  exact_mod_cast h

theorem vDiff_spec (D : D7) (p : ℕ) : 0 ≤ vDiff D.host.E p ∧ (DV.UnramE D p → vDiff D.host.E p = 0) ∧
    (p.Prime → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
      (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 D.host.E)) : ℝ) = (eWL D.host.E w : ℝ) * vDiff D.host.E p) := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), fun h => ?_, fun hp w hw => ?_⟩
  · rw [vDiff, padicValNat.eq_zero_of_not_dvd h, Nat.cast_zero, zero_div]
  · haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    exact multiplicity_different_eq _ hp w hw

end GlobalTheory.ShFam.Pad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
section
noncomputable section

namespace GlobalTheory.CuspFrom

section Analytic

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD

def FlowMajSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom → ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0 →
      X.maj (X.flow ξ s x) τ v = X.maj x τ v +
        ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
          (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ))) ∧
    ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (v w : Fin r → ℂ),
      ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w ∧ ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w

def OrbitThickSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∀ x ∈ X.dom, ∃ ε : ℝ, 0 < ε ∧ ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom →
      ∏ τ, X.tt ξ (X.flow ξ s x) τ = ∏ τ, X.tt ξ x τ → ε ≤ X.la1 (X.flow ξ s x)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def ThickBdd (φ : Frame X.Ψ r → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x ∈ X.dom, ε ≤ X.la1 x → φ x ≤ C

def FreqNonneg (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ

def StepBound (w : ℝ) (φ : Frame X.Ψ r → ℝ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ q : X.Ψ → ℝ, (∀ τ, 0 < q τ ∧ q τ ≤ 1) → ∀ B : ℝ,
    (∀ s : X.Ψ → ℝ, φ (X.flow ξ (fun τ => (s τ : ℂ) + I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ)) x) ≤ B) →
    φ x ≤ B * ∏ τ, q τ ^ (-w)

end Analytic

section Geometric

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Toroidal GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def FlowTie {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} [Algebra (FractionRing ℂ) ℂ] (Uw : UnfWit U)
    {O : Type} [CommRing O] {β : O →+* c.F} (a : ArcIn Dw l β ℂ (σ.comp β)) (k : U.Comp) (ξ' : Fin r → E)
    (x : Frame (U.X k).Ψ r) : Prop :=
  ∀ (Y : Model Xo c β) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F),
    ∃ (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)),
      (∀ τ, 0 < d τ) ∧ (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) ∧
      ∀ w : ℂ, T < w.im → ∃ hx : (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom,
        AnLie Uw.F Ha.i (Ha.Pw w) (U.un k ⟨_, hx⟩) z

def BdExt {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {V K : Type} [CommRing V] [IsLocalRing V] [Field K]
    [Algebra V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) : Prop :=
  ∃ (χ : Sp V ⟶ gen Z) (g : EigFrame Z φ (χ ≫ genι Z)), χ ≫ genStr Z = spMap φ ∧
    GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ ∧
    (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y ∧
      w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap V K)) ≫ g.v τ i) ∧
    χ (IsLocalRing.closedPoint V) ∈ genBd Z

end Geometric

end GlobalTheory.CuspFrom
end
end

