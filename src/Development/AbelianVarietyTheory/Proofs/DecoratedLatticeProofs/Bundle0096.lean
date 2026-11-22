import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceFormRealCoordinatesIntegralGram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoublingChartInertPlace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.DblInert

open Formalism.UG GlobalTheory.LFun.InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {σ : E →ₐ[F] E} {h : w.under (𝓞 F) = v}
  {c : w.adicCompletion E →+* w.adicCompletion E} {m : ℕ}

theorem bc_mem_iff_gram (hw : IsInertAt F E v w) (hc : GlobalTheory.LFun.IsConjAt σ h c) {J : Matrix (Fin m) (Fin m) E}
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {a : GL (Fin m) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = T) (g : GL (Fin m) (Fv F v ⊗[F] E)) :
    g ∈ HR (Fv F v) σ J ↔ a⁻¹ * bc (toCompl h) g * a ∈ UJ c T := by
  have h1 : cT c (bc (toCompl h) g).1 = (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1).map (toCompl h) :=
    Matrix.ext fun i j => hc _
  have h2 : g ∈ HR (Fv F v) σ J ↔ bc (toCompl h) g ∈ UJ c (J.map (algebraMap E _)) := by
    change _ ↔ cT c (bc (toCompl h) g).1 * _ * g.1.map (toCompl h) = _
    rw [h1, ← JR_map h, ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (toCompl_bijective hw h).1).eq_iff.symm
  have h3 : ∀ x : GL (Fin m) (w.adicCompletion E), cT c (a⁻¹ * x * a).1 * T * (a⁻¹ * x * a).1 =
      cT c a.1 * (cT c x.1 * J.map (algebraMap E _) * x.1) * a.1 := fun x => by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc,
      mul_inv_cancel_left, Units.val_mul, cT_mul]
    simp only [Matrix.mul_assoc]
  have h4 : IsUnit (cT c a.1) := IsUnit.of_mul_eq_one (cT c (a⁻¹).1) (by rw [← cT_mul, Units.inv_mul, cT_one])
  rw [h2]
  change _ ↔ _ * _ * _ = _
  rw [h3, ← ha, a.isUnit.mul_left_inj, h4.mul_right_inj]
  rfl

def chartGram (hw : IsInertAt F E v w) (hc : GlobalTheory.LFun.IsConjAt σ h c) {J : Matrix (Fin m) (Fin m) E}
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {a : GL (Fin m) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = T) : GLoc σ J v ≃* UJ c T :=
  have e1 : ∀ x : GL (Fin m) (w.adicCompletion E), bc (toCompl h) (bc (complEquiv hw h).symm.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).apply_symm_apply _)
  have e2 : ∀ x : GL (Fin m) (Fv F v ⊗[F] E), bc (complEquiv hw h).symm.toRingHom (bc (toCompl h) x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).symm_apply_apply _)
  { toFun := fun g => ⟨a⁻¹ * locMat σ J h g * a, (bc_mem_iff_gram hw hc ha _).1 g.2⟩
    invFun := fun u => ⟨bc (complEquiv hw h).symm.toRingHom (a * u * a⁻¹), (bc_mem_iff_gram hw hc ha _).2 (by
      rw [e1, show a⁻¹ * (a * u * a⁻¹) * a = u by group]; exact u.2)⟩
    left_inv := fun g => Subtype.ext ((congrArg (bc (complEquiv hw h).symm.toRingHom)
      (show a * (a⁻¹ * locMat σ J h g * a) * a⁻¹ = locMat σ J h g by group)).trans (e2 g.1))
    right_inv := fun u => Subtype.ext ((congrArg (a⁻¹ * · * a) (e1 _)).trans (by group))
    map_mul' := fun g g' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }

section Conj

variable {A B n ι : Type} [CommRing A] [CommRing B] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
  (e : n ⊕ n ≃ ι)

theorem blkGL_mem_diag (a : GL n A) : blkGL e (a, a) ∈ stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 ((keepsDiag_blkMat e).2 rfl)

theorem conj_mem_diag (a : GL n A) (x : GL ι A) :
    (blkGL e (a, a))⁻¹ * x * blkGL e (a, a) ∈ stabGL (diagSub A e) ↔ x ∈ stabGL (diagSub A e) := by
  rw [Subgroup.mul_mem_cancel_right _ (blkGL_mem_diag e a),
    Subgroup.mul_mem_cancel_left _ (inv_mem (blkGL_mem_diag e a))]

theorem bc_mem_diag {f : A →+* B} (hf : Function.Injective f) (x : GL ι A) :
    bc f x ∈ stabGL (diagSub B e) ↔ x ∈ stabGL (diagSub A e) := by
  rw [mem_stabGL_diagSub, mem_stabGL_diagSub]
  refine ⟨fun hx => (keepsDiag_iff e).2 fun i j => hf ?_, fun hx => hx.map e f⟩
  rw [map_add, map_add]
  exact (keepsDiag_iff e).1 hx i j

theorem det_leviMat_conj (a : GL n A) {x : GL ι A} (hx : x ∈ stabGL (diagSub A e)) :
    (leviMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (leviMat e x.1).det := by
  let D : stabGL (diagSub A e) →* Aˣ := Matrix.GeneralLinearGroup.det.comp (leviGL e)
  let b : stabGL (diagSub A e) := ⟨_, blkGL_mem_diag e a⟩
  have h1 : D (b⁻¹ * ⟨x, hx⟩ * b) = D ⟨x, hx⟩ := by
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  exact congrArg Units.val h1

end Conj

theorem exists_dblChart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ (c : w.adicCompletion E →+* w.adicCompletion E) (e : GLoc σ J v ≃* GU c n), IsInertChart σ J L h c e → ∃ f : GLoc σ Q v ≃* GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD c n, (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD c n) ∧ (∀ y, f (ioH _ σ hQ (y, 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n) ∧ ∀ (p : siegelH (Fv F v) σ Q) (hp : f p ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n ⟨f p, hp⟩ = Units.map (toCompl h).toMonoidHom (aH _ σ Q p) := by
  intro F E _ _ _ _ _ σ _ n J _ Q hQ L _ v w h hw c e he
  obtain ⟨hc, ⟨a, ha', ha, hea⟩, -⟩ := he
  have hA' : IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal E w n L a ha'
  have hT : cT c (blkGL finSumFinEquiv (a, a)).1 * Q.map (algebraMap E _) * (blkGL finSumFinEquiv (a, a)).1 =
      dblGram finSumFinEquiv (antiJ (w.adicCompletion E) n) := by
    rw [hQ, dblGram, blkMat_map _ _ (map_zero _), val_blkGL, cT_blkMat, blkMat_mul, blkMat_mul, ha,
      Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul, ha]
    rfl
  have hinj := (toCompl_bijective hw h).1
  refine ⟨chartGram hw hc hT, fun g => ?_, fun y => Subtype.ext ?_, fun g => ?_, fun p hp => Units.ext ?_⟩
  · refine Iff.trans ?_ (((isFrameAt_mul hA' (one_mem _)).2 (locMat σ Q h g)).trans
      ⟨fun hg => ⟨(chartGram hw hc hT g).2, hg⟩, fun hg => hg.2⟩)
    rw [mem_stabLoc]
    refine ⟨fun hg z => ?_, fun hg y => ?_⟩
    · obtain ⟨y, rfl⟩ := exists_comp h z
      rw [← mem_latLoc_iff hw, hg, mem_latLoc_iff hw h, comp_mulVec]
      rfl
    · rw [mem_latLoc_iff hw h, hg, mem_latLoc_iff hw h, comp_mulVec]
      rfl
  · change (blkGL finSumFinEquiv (a, a))⁻¹ * bc (toCompl h) (blkGL finSumFinEquiv
      (GlobalTheory.AdelicU.matHom _ σ J y, GlobalTheory.AdelicU.matHom _ σ J 1)) * blkGL finSumFinEquiv (a, a) =
        blkGL finSumFinEquiv ((e y : GL (Fin n) (w.adicCompletion E)), 1)
    rw [bc_blkGL, ← map_inv, ← map_mul, ← map_mul, hea, map_one, map_one, Prod.inv_mk, Prod.mk_mul_mk,
      Prod.mk_mul_mk, mul_one, inv_mul_cancel]
    rfl
  · exact ((conj_mem_diag finSumFinEquiv a _).trans (bc_mem_diag finSumFinEquiv hinj _)).symm
  · refine (det_leviMat_conj finSumFinEquiv a ((bc_mem_diag finSumFinEquiv hinj _).2 p.2)).trans ?_
    exact (congrArg Matrix.det (leviMat_map finSumFinEquiv (toCompl h) _)).trans (RingHom.map_det _ _).symm

end GlobalTheory.DblInert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormMapRBijective
section
noncomputable section

namespace GlobalTheory.Core.ColZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (pr : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)
  (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}

def clMapR (c : ((stepY ST y β Λ Θ pref).reRep pr).Cl) : (base ST lam Λ₀).Cl :=
  (base ST lam Λ₀).cls (((stepY ST y β Λ Θ pref).reRep pr).rep c).1.1.deco

theorem clMapR_cl (hΛ : ∀ b, Λ b = Λ₀) (b : β) (p : (stepY ST y β Λ Θ pref).D b) :
    clMapR (Λ₀ := Λ₀) pref pr lam (((stepY ST y β Λ Θ pref).reRep pr).cl b p) = (base ST lam Λ₀).cls p.1.1.deco := by
  have e := congrArg (fun q : (stepY ST y β Λ Θ pref).D b => q.1.1.deco) (((stepY ST y β Λ Θ pref).reRep pr).mv_smul b p)
  rw [← e]
  exact ((base ST lam Λ₀).cls_smul (down (y := y) pref hΛ b (((stepY ST y β Λ Θ pref).reRep pr).mv b p)) _).symm

theorem clMapR_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    Function.Bijective (clMapR (Λ₀ := Λ₀) pref pr lam) := by
  refine ⟨?_, fun c₀ => ?_⟩
  · rintro ⟨b, q⟩ ⟨b', q'⟩ h
    obtain rfl : b = b' := Subsingleton.elim (α := β) _ _
    obtain ⟨g₀, hg⟩ := ((base ST lam Λ₀).cls_eq_iff _ _).1 h
    obtain ⟨g, -, h2⟩ := exists_lift pref hy hΛ hΘ b _ _ g₀ hg
    congr 1
    rw [← ((stepY ST y β Λ Θ pref).reRep pr).rp_spec b q, ← ((stepY ST y β Λ Θ pref).reRep pr).rp_spec b q']
    exact Quotient.sound ⟨g, h2⟩
  · induction c₀ using Quotient.inductionOn' with
    | h d =>
      obtain ⟨p, rfl⟩ := exists_pt (Q := Q) hy d
      exact ⟨((stepY ST y β Λ Θ pref).reRep pr).cl default p, clMapR_cl pref pr lam hΛ default p⟩

def clEquivR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    ((stepY ST y β Λ Θ pref).reRep pr).Cl ≃ (base ST lam Λ₀).Cl :=
  Equiv.ofBijective _ (clMapR_bijective pref pr lam hy hΛ hΘ)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pr).rep ((clEquivR pref pr lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := (clEquivR pref pr lam hy hΛ hΘ).apply_symm_apply c

def formMapR (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q)
    (h : (((stepY ST y β Λ Θ pref).reRep pr).fam X.emb lam).Ok) :
    (base ST lam Λ₀).EqFun →ₗ[X.K] ((stepY ST y β Λ Θ pref).reRep pr).FormsK X.emb lam h where
  toFun φ := ⟨fun c => φ.1 (((stepY ST y β Λ Θ pref).reRep pr).rep c).1.1.deco, fun c g =>
    (form_smul pref lam hΛ hΘ φ c.1 g.1 _).symm.trans (congrArg (fun q => φ.1 q.1.1.deco) g.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem formMapR_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (h : (((stepY ST y β Λ Θ pref).reRep pr).fam X.emb lam).Ok)
    (h₀ : (base ST lam Λ₀).Ok) :
    Function.Bijective (formMapR pref pr lam hΛ hΘ h) := by
  refine ⟨fun φ ψ e => ?_, fun f => ?_⟩
  · apply ((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).injective
    apply Subtype.ext
    funext c
    exact congrFun (congrArg Subtype.val e) ((clEquivR pref pr lam hy hΛ hΘ).symm c)
  · let f₀ : ((base ST lam Λ₀).toCSDOf h₀ (secR pref pr lam hy hΛ hΘ)).Forms :=
      ⟨fun c => f.1 ((clEquivR pref pr lam hy hΛ hΘ).symm c), fun c g₀ => by
        obtain ⟨g, h1, h2⟩ := exists_lift pref hy hΛ hΘ _ _ _ g₀.1 g₀.2
        have h3 := f.2 ((clEquivR pref pr lam hy hΛ hΘ).symm c) ⟨g, h2⟩
        have h4 := rho_eq pref lam hΛ hΘ _ g
        rw [h1] at h4
        exact (LinearMap.congr_fun h4 _).symm.trans h3⟩
    refine ⟨((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).symm f₀, Subtype.ext (funext fun c => ?_)⟩
    obtain ⟨c₀, rfl⟩ := (clEquivR pref pr lam hy hΛ hΘ).symm.surjective c
    exact congrFun (congrArg Subtype.val
      (((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).apply_symm_apply f₀)) c₀

end Forget

theorem exists_colZeroR {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
    {G : ChGlob X R.m} {m2 : ℕ} (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)
    (pr : ∀ b, (stepAt sel mu cst L Tp u 0).D b → Prop) (hX : X.Ok) (hL : L.Ok Ch sel mu cst G m2)
    (h : (((stepAt sel mu cst L Tp u 0).reRep pr).fam X.emb (lamT (W.hc u) 0)).Ok) :
    ∃ κ : MfV W Ch u ≃ₗ[X.K] ((stepAt sel mu cst L Tp u 0).reRep pr).FormsK X.emb (lamT (W.hc u) 0) h,
      ∀ φ c, (κ φ).1 c = φ.1 (((stepAt sel mu cst L Tp u 0).reRep pr).rep c).1.1.deco :=
  letI := idxUnique hL
  ⟨LinearEquiv.ofBijective _ (formMapR_bijective (Tp.pref u 0) pr (lamT (W.hc u) 0) (ysAt_zero sel mu cst)
    (levGAt_zero Tp hL) (levQAt_zero Tp hL) h (colOk W Ch hX u 0)), fun _ _ => rfl⟩

end GlobalTheory.Core.ColZero

namespace GlobalTheory.Core.ColZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_colEquiv {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws)
    (u : B.Word) (a : I.ι) :
    ∃ κ : ColsK I u ≃ₗ[B.fields.K] ((I.fm l u a).lat 0).V, ∀ φ, IsCol I u a l (κ φ) φ :=
  exists_colZeroR (Pr := B.primes X) B.wts (I.Tp a) u (I.pref u a 0) hX (h.idx_ok a) ((l.fmL u a).fam 0)

end GlobalTheory.Core.ColZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameFamilyCompactRepresentation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.SepTypes

theorem coeffSpan_finiteDimensional {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) : FiniteDimensional ℂ (coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | (apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients ..)

theorem coeffSpan_rtrans {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (c : G) {h : G → ℂ} (hh : h ∈ coeffSpan ρ) :
    (fun k => h (k * c)) ∈ coeffSpan ρ := by
  have hle : coeffSpan ρ ≤ (coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (fun k : G => k * c)) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine Submodule.subset_span ⟨ℓ, ρ c w, funext fun k => ?_⟩
    simp [LinearMap.funLeft, map_mul]
  exact hle hh

theorem exists_space {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Γ : ι → Type} [∀ i, Group (Γ i)] (K : Subgroup G) (j : (∀ i, Γ i) →* K)
    (hjs : Function.Surjective j) (a : ∀ i, Γ i → G) (hj : ∀ i k, (j (Pi.mulSingle i k) : G) = a i k)
    (W : ι → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)]
    (ρ : ∀ i, Representation ℂ (Γ i) (W i)) :
    ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧
      (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧
      ∀ φ : G → ℂ, Continuous φ → (∀ i x, (fun k => φ (x * a i k)) ∈ coeffSpan (ρ i)) →
        ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  let S : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ τ (k₀ : K), (fun κ => f (k₀ * j (Pi.mulSingle τ κ))) ∈ coeffSpan (ρ τ)}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun τ k₀ => Submodule.add_mem _ (ha.2 τ k₀) (hb.2 τ k₀)⟩
      zero_mem' := ⟨continuous_const, fun τ k₀ => Submodule.zero_mem _⟩
      smul_mem' := fun c {a} ha => ⟨ha.1.const_smul c, fun τ k₀ => Submodule.smul_mem _ c (ha.2 τ k₀)⟩ }
  have hfd : ∀ τ, FiniteDimensional ℂ (coeffSpan (ρ τ)) := fun τ => coeffSpan_finiteDimensional (ρ τ)
  have hfin := GlobalTheory.finiteDimensional_span_separately ι Γ (fun τ => coeffSpan (ρ τ)) hfd
  have hupd : ∀ (x : ∀ τ, Γ τ) τ y,
      Function.update x τ y = Function.update x τ 1 * Pi.mulSingle τ y := by
    intro x τ y
    funext τ'
    by_cases h : τ' = τ
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
  let M := Submodule.span ℂ {F : (∀ τ, Γ τ) → ℂ |
    ∀ τ x, (fun y => F (Function.update x τ y)) ∈ coeffSpan (ρ τ)}
  let T : S →ₗ[ℂ] M :=
    { toFun := fun f => ⟨fun x => (f : K → ℂ) (j x), Submodule.subset_span fun τ x => by
        have := f.2.2 τ (j (Function.update x τ 1))
        convert this using 2 with y
        rw [hupd x τ y, map_mul]⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hT : Function.Injective T := by
    intro a b hab
    have := congrArg (fun u : M => (u : (∀ τ, Γ τ) → ℂ)) hab
    apply Subtype.ext
    funext k
    obtain ⟨x, rfl⟩ := hjs k
    exact congrFun this x
  refine ⟨S, Module.Finite.of_injective T hT, fun f hf => hf.1, ?_, ?_⟩
  · intro f hf k
    refine ⟨hf.1.comp (continuous_id.mul continuous_const), fun τ k₀ => ?_⟩
    obtain ⟨κ₁, rfl⟩ := hjs k
    have key : ∀ κ, k₀ * j (Pi.mulSingle τ κ) * j κ₁ =
        (k₀ * j (Function.update κ₁ τ 1)) * j (Pi.mulSingle τ (κ * κ₁ τ)) := by
      intro κ
      rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul]
      congr 2
      funext τ'
      by_cases h : τ' = τ
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    simp only [key]
    exact coeffSpan_rtrans (ρ τ) (κ₁ τ) (hf.2 τ _)
  · intro φ hφ hty g
    refine ⟨hφ.comp (continuous_const.mul continuous_subtype_val), fun τ k₀ => ?_⟩
    have := hty τ (g * (k₀ : G))
    simpa only [Subgroup.coe_mul, hj, mul_assoc] using this

end GlobalTheory.SepTypes

theorem GlobalTheory.typesFiniteSpace : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ K : Subgroup (GA D V), (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧ (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧ ∀ φ : GA D V → ℂ, Continuous φ → (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) → ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  intro D θ _ V ε fr _ K ⟨j, hjs, hj⟩ W _ _ _ ρ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact GlobalTheory.SepTypes.exists_space K j hjs (fun τ k => kAt θ V τ (ε τ) (fr τ) k) hj W ρ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NrmStepZeroEq
section
noncomputable section

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}
  (pf : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := by
    obtain ⟨⟨b, q⟩, rfl⟩ := (clEquiv pref lam hy hΛ hΘ).surjective c
    rw [Equiv.symm_apply_apply]
    refine (clMap_cl (Θ := Θ) pref lam hΛ b _).symm.trans ?_
    exact congrArg (fun q => clMap (y := y) (Λ := Λ) (Θ := Θ) (Λ₀ := Λ₀) pref lam ⟨b, q⟩) (((stepY ST y β Λ Θ pref).reRep pf).rp_spec b q)

theorem majAt_eq_ipAt [Unique β] (hX : X.Ok) (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (hS : ((stepY ST y β Λ Θ pref).reRep pf).Ok)
    (h : (((stepY ST y β Λ Θ pref).reRep pf).fam X.emb lam).Ok) (h₀ : (base ST lam Λ₀).Ok) (hr : (base ST lam Λ₀).Rat)
    (v : InfinitePlace X.K) (x : ((stepY ST y β Λ Θ pref).reRep pf).FormsK X.emb lam h) (φ : (base ST lam Λ₀).EqFun)
    (hx : ∀ c, x.1 c = φ.1 (((stepY ST y β Λ Θ pref).reRep pf).rep c).1.1.deco) :
    Formalism.HermitianLatticesTheory.majAt (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).b
      (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).X v x x = (base ST lam Λ₀).ipAt h₀ v φ φ := by
  obtain ⟨σ, hσ⟩ := hX.conjK
  have hF : FOk X.emb σ := ⟨hX.conjE, hX.emb_star, hσ⟩
  refine (majAt_eq_classSum (((stepY ST y β Λ Θ pref).reRep pf).csd X.emb lam h) (GlobalTheory.Mem.LatGood.hasRatBasis _ _ σ lam hF hS h)
    (fun v => GlobalTheory.Mem.LatGood.step_gram_posDef _ _ σ lam hF hS h v.embedding) v _ _).trans ?_
  rw [hr.ipAt_indep h₀ (secR pref lam pf hy hΛ hΘ)]
  refine (@Fintype.sum_equiv _ _ _ (_) (_) _ (clEquiv pref lam hy hΛ hΘ).symm _ _ fun c => ?_).symm
  rw [hx]
  congr 3
  refine (card_stab pref hy hΛ hΘ ((clEquiv pref lam hy hΛ hΘ).symm c).1 (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c))).symm.trans ?_
  exact @Nat.card_eq_fintype_card _ (_)

end Forget

end GlobalTheory.Core.ColNorm

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem nrm_stepZero_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u), IsCol I u a l x φ → ∀ v, nrm ((I.fm l u a).lat 0) v x = nrm (Mu0H (Pr := B.primes X) B.wts I.Ch hX u) v φ := by
  intro B X I h hX l u a x φ hc v
  have hL := h.idx_ok a
  letI := StepZero.idxUnique hL
  have key := majAt_eq_ipAt ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (I.pref u a 0) hX
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a)) (StepZero.levGAt_zero (I.Tp a) hL) (StepZero.levQAt_zero (I.Tp a) hL)
    ((l.ch u a).step 0) ((l.fmL u a).fam 0) (colOk (Pr := B.primes X) B.wts I.Ch hX u 0) (colRat (Pr := B.primes X) B.wts I.Ch hX u 0) v x φ hc
  have key2 := key.trans (latH_maj (Pr := B.primes X) B.wts I.Ch hX u 0 v φ φ).symm
  have h1 := normAt_sq_eq_majAt ((I.fm l u a).lat 0).b ((I.fm l u a).lat 0).X v x
  have h2 := normAt_sq_eq_majAt (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).b (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).X v φ
  exact (pow_left_inj₀ (normAt_nonneg _ _ _ _) (normAt_nonneg _ _ _ _) two_ne_zero).1
    (h1.trans ((congrArg Complex.re key2).trans h2.symm))

end GlobalTheory.Core.ColNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PointDeterminantDiamondOperatorInvariant
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section
namespace GlobalTheory.KerDia.RhoDia

section Gen
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pointDeterminant_diamondOperator_invariant {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {n : ℕ}
    {ST SG Q : Finset (HeightOneSpectrum (𝓞 H.E))} (p q : DecoF H.E n ST SG Q) (P : ST) (c : (𝓞 H.E ⧸ P.1.asIdeal)ˣ)
    (hd : q.deco = DecoSet.dia1 P c p.deco) (hfr : q.fr = p.fr) : detPt H SQ q = detPt H SQ p := by
  have hN : q.deco.1.N = p.deco.1.N := by rw [hd]; rfl
  have hbe : q.deco.1.be = p.deco.1.be := by rw [hd]; rfl
  have h := ptFr_congr (p := q) (p' := p) hN hbe hfr
  unfold detPt ptIdl
  rw [h, hN]

end Gen

theorem rho_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (p : (I.stp u a i).D b) (b' : (I.stp u a (i + 1)).β) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.rho u a i b (((I.atIn u a).A i).dia b P s p) = I.rho u a i b p ∧ I.rho' u a i b' (((I.atIn u a).A (i + 1)).dia b' P s p') = I.rho' u a i b' p' := by
  intro B X I _ u a i b p b' p' P s
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p P s
  obtain ⟨h1', h2', -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p' P s
  have e := pointDeterminant_diamondOperator_invariant B.host I.SQ p.1.1 _ P s h1 h2
  have e' := pointDeterminant_diamondOperator_invariant B.host I.SQ p'.1.1 _ P s h1' h2'
  constructor
  · show ((rhoAt I.SQ I.C (I.xi a) i (p.mv (DecoSet.dia1 P s p.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)
    rw [rhoAt_eq, rhoAt_eq, e]
  · show ((rhoAt' I.SQ I.C (I.xi a) i (p'.mv (DecoSet.dia1 P s p'.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt' I.SQ I.C (I.xi a) i p'.1.1 : ℂˣ) : ℂ)
    rw [rhoAt'_eq, rhoAt'_eq, e']

end GlobalTheory.KerDia.RhoDia
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothVecHeadOfDerivativeFamilyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVec_head_of_derivative_family : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → ∀ v ∈ GlobalTheory.TypeSum.Fam ε σ, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v []) := by
  first | exact @GlobalTheory.FamSmooth.famSmooth | exact GlobalTheory.FamSmooth.famSmooth | (intros; apply GlobalTheory.FamSmooth.famSmooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpanStatement
section
open Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_weyl_module_maps_injective_on_pure_span : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ι → ℕ) (b : ∀ τ, Module.Basis (Fin (d τ)) ℂ (V τ)), (∀ τ ξ, j τ ξ ∈ delSq ℂ n (lam τ)) → (∀ τ, ∀ p ∈ delSq ℂ n (lam τ), ∃ ξ, j τ ξ = p) → (∀ τ a a', normFock (lam τ) (j τ (b τ a)) (j τ (b τ a')) = if a = a' then 1 else 0) → ∃ Jt : (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, Function.Injective Jt ∧ LinearMap.range Jt = CSpan lam ∧ ∀ x : (∀ τ, V τ), Jt (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  first | exact @GlobalTheory.TenInj.main | exact GlobalTheory.TenInj.main | (intros; apply GlobalTheory.TenInj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceFormRealCoordinatesIntegralGramStatement
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceForm_real_coordinates_integral_gram : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)), IsRealCoord I ρ → ∃ (X : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) (c : ℕ), μ ≠ 0 ∧ 1 ≤ c ∧ ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ B B' : Matrix (Fin N) (Fin N) ℤ, B.map (Int.cast : ℤ → ℝ) = (gm I ρ y e)ᵀ * X * gm I ρ y e ∧ gm I ρ y e * B'.map (Int.cast : ℤ → ℝ) * (gm I ρ y e)ᵀ = μ • X ∧ ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j) := by
  first | exact @GlobalTheory.CuspGeo.TrReal.trace_form_real_coord | exact GlobalTheory.CuspGeo.TrReal.trace_form_real_coord | (intros; apply GlobalTheory.CuspGeo.TrReal.trace_form_real_coord <;> assumption)
end

