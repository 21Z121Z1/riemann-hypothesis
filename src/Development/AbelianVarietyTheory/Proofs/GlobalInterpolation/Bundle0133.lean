import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
import Formalism.LocalToGlobal.Columns.AtTOwedV
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0130
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryCoordinateAlgebraDense
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SameOfAbove
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.UpLaw

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β]
  {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q} {pref : DecoF X.E n ST SG Q → Prop} {T : ℕ} {P : ST}
  (hP : MoveHyp ST SG P) (hT : (T : 𝓞 X.E) ∈ P.1.asIdeal ∧ (T : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
  (hQ : ∀ w : Q, w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1) (hy : y.Off P.1)

include hP hT hQ hy

theorem above_iff (b : β) (p q : PtY ST SG Q y) : Above (tdatY ST T y β Λ Θ pref) b P p q ↔
    p.1.1.deco.1.IsUp P (T : 𝓞 X.E) q.1.1.deco.1 ∧ q.1.1.1.2 = p.1.1.1.2 ∧ q.1.2 = p.1.2 := by
  constructor
  · rintro ⟨x, hx, hf, rfl⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨⟨x, hx, hf, h.1⟩, h.2⟩
  · rintro ⟨⟨x, hx, hf, e⟩, h2, h3⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨x, hx, hf, PtY.ext' (Subtype.ext (e.trans h.1.symm)) (h2.trans h.2.1.symm) (h3.trans h.2.2.symm)⟩

theorem bijOn_up (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P p q} {d | p.1.1.deco.1.IsUp P (T : 𝓞 X.E) d.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b p q).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b p q).1 hq).2
    have h' := ((above_iff hP hT hQ hy b p q').1 hq').2
    exact PtY.ext' e (h.1.trans h'.1.symm) (h.2.trans h'.2.symm)
  · obtain ⟨x, hx, hf, e⟩ := hd
    exact ⟨_, ⟨x, hx, hf, rfl⟩, Subtype.ext ((mv_up T p P hP hT hQ hy hx hf).1.trans e.symm)⟩

theorem bijOn_dn (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P q p} {d | d.1.IsUp P (T : 𝓞 X.E) p.1.1.deco.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b q p).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b q p).1 hq).2
    have h' := ((above_iff hP hT hQ hy b q' p).1 hq').2
    exact PtY.ext' e (h.1.symm.trans h'.1) (h.2.symm.trans h'.2)
  · have hs := fun w h1 h2 => (Deco.IsUp.sameAt d.2 hP hd (Q := w) h1 h2).localization_eq.symm
    have h := p.mv_spec d (fun w => hs w.1 (hQ w).1 (hQ w).2) (hy _ _ hs)
    refine ⟨p.mv d, (above_iff hP hT hQ hy b _ p).2 ⟨?_, h.2.1.symm, h.2.2.symm⟩, h.1⟩
    rw [h.1]
    exact hd

theorem same_of_above (b : β) {p q : PtY ST SG Q y} (h : Above (tdatY ST T y β Λ Θ pref) b P p q) :
    SameOff ST p.1.1.deco.1.N q.1.1.deco.1.N ∧ p.1.1.deco.1.be = q.1.1.deco.1.be ∧ p.1.1.fr = q.1.1.fr ∧ p.1.2 = q.1.2 := by
  obtain ⟨h1, h2, h3⟩ := (above_iff hP hT hQ hy b p q).1 h
  exact ⟨fun w hw => (h1.sameAt p.1.1.deco.2 hP (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm, h1.be_eq.symm,
    funext fun w => (congrFun h2 w).symm, h3.symm⟩

end Gen

theorem kAt_uk : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → GlobalTheory.KerT.UKTerm W Ch sel mu cst A u i (i + 1) → ∀ b b' (d : (stepAt sel mu cst L Tp u i).D b) (d' : (stepAt sel mu cst L Tp u (i + 1)).D b') (P : Pr.vT u) F, (∑ᶠ d₁ ∈ {d₁ | Above (tdatAt sel mu cst L Tp u (i + 1)) b' P d' d₁}, kAt W Ch sel mu cst L A u i b b' d d₁ F) = ((Pr.T u : X.K) ^ ((R.t + 1) / 2)) • ∑ᶠ d₀ ∈ {d₀ | Above (tdatAt sel mu cst L Tp u i) b P d₀ d}, kAt W Ch sel mu cst L A u i b b' d₀ d' F := by
  intro X Pr R W Ch sel S mu cst L G m2 u i hX hPr hsel hS _ Tp A hK hU b b' d d' P F
  obtain ⟨Ξ₀, hb, -, -, -, hk⟩ := hK b b' d d'
  have hP := moveHyp_of_ok hPr u P
  have hT := T_unif hX hPr u P
  have hQ0 := T_notMem_QE sel mu u hPr hsel hS
  have hQ : ∀ w : QE sel (mu : Chr X.F X.E X.K), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun w => ne_of_T_notMem hPr u P (hQ0 w.1 w.2)
  have hy := fun j => ysAt_off (R := R) sel mu cst hPr u hQ0 j P
  have refl : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p p :=
    fun p => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have key := hU d.1.1.deco (frsF sel mu d.1.1) d'.1.1.deco (frsF sel mu d'.1.1) Ξ₀ P F hP hP hb
  refine (finsum_mem_eq_of_bijOn _ (bijOn_up hP hT hQ (hy (i + 1)) b' d') fun q hq => ?_).trans
    (key.trans (congrArg _ (finsum_mem_eq_of_bijOn _ (bijOn_dn hP hT hQ (hy i) b d) fun q hq => ?_).symm))
  · rw [hk d q (refl d) (same_of_above hP hT hQ (hy (i + 1)) b' hq)]
  · obtain ⟨h1, h2, h3, h4⟩ := same_of_above hP hT hQ (hy i) b hq
    rw [hk q d' ⟨fun w hw => (h1 w hw).symm, h2.symm, h3.symm, h4.symm⟩ (refl d')]

end GlobalTheory.LvT.Built.UpLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.ChiDet

theorem tildeQ_detPt_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : GlobalTheory.Mem.Chr.HFrame H e) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))), letI := H.cmStar; ∀ (p : DecoF H.E n ST SG Q), LevOk H SG SQ → ((tildeQ H SQ C.chiPsi (detPt H SQ p) : ℂˣ) : ℂ) = chiId C.chiPsi (Th.detId H (Th.stdL H n) p.deco.1.N) := by
  intro R H e C n ST SG Q SQ
  letI := H.cmStar
  intro p hL
  have hχ := C.isChi
  have hK := (GlobalTheory.Mem.KerDet.kernel_open_and_factor R H).2.2.2 C.chiPsi hχ.triv (fun v y hy _ => hχ.unr v y hy)
    fun v _ => hχ.unr v
  rw [tildeQ_eq_comp H SQ hK, MonoidHom.comp_apply]
  exact tildeD_eq_chiId R H C.chiPsi hχ n _ p.deco.2.lat _
    (congrArg (toDtTMod H SQ) (mk_detPt_eq_relDetQ R H n ST SG Q SQ p hL))

end GlobalTheory.Mem.ChiDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslatePrimeToOrderPreservesThetaIntegralityStatement
section
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_primeToOrder_preserves_theta_integrality : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), Per S.d ι δ₀ θ Ω → S.Ok → GlobalTheory.MomOne.Split S.d q → S.IsTheta e → S.AlgJets δ₀ e → S.PrimeTo q t → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup e → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup (opU S.Hm t e) := by
  first | exact @GlobalTheory.MomTrans.latInt_translate | exact GlobalTheory.MomTrans.latInt_translate | (intros; apply GlobalTheory.MomTrans.latInt_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUniStatement
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentTypeLevel_character_finiteOrder_rootsOfUnity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (a t skip fc : ℕ) (zl : Bool) (_ : GLev S G a t 0 skip fc zl) (K : Type) [Field K] (s : K →+* ℂ), (∀ i, (gp i).Prime) → (∀ i, ∃ ζ : K, IsPrimitiveRoot ζ (gp i)) → ∃ N : ℕ, 0 < N ∧ ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.unipotent_type_character_finite_order | exact GlobalTheory.unipotent_type_character_finite_order | (intros; apply GlobalTheory.unipotent_type_character_finite_order <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryCoordinateAlgebraDenseStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_coordinate_algebra_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, Continuous p) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, star p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, p x ≠ p y) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ b i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  first | exact @GlobalTheory.PolyRealU.poly_infU | exact GlobalTheory.PolyRealU.poly_infU | (intros; apply GlobalTheory.PolyRealU.poly_infU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryStandardAtQFromIsometryOverField
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.KapIsom

theorem form_u (D : D7) (L : PeriodPair) (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (hu : Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (x y : Fin 4 × D.what₂.Tau → ℂ) :
    ∑ w, u x w * (starRingEnd ℂ) (u y w) = ∑ w, x w * (starRingEnd ℂ) (y w) := by
  have h := hu x y
  change Formalism.L2.Th1.H.matH (hOne L _) (u x) (u y) = Formalism.L2.Th1.H.matH (hOne L _) x y at h
  rw [matH_hOne, matH_hOne] at h
  have hA : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos L).ne'
  exact (div_left_inj' hA).1 h

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∃ γ : IsoK D, γ.AtP q ∧ LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) = D.host.φ₀ ((γ.detRel B.γ₀ : D.host.K) : D.host.E) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hqc ι u hu h1 h2 h3
  obtain ⟨G, hG, hdet⟩ := GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) u
    (GlobalTheory.T.unitary_fourfoldLattice_preserves_rationalVectors D cc δ B hcc u h1)
  have hG' : ∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E))
      = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E) := fun v => hG v
  let γ : IsoK D :=
    { g := B.γ₀.g.trans G
      isom := by
        intro x y
        apply D.host.φ₀.injective
        have e1 := form_u D B.L u hu (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E))
          (fun w => D.host.φ₀ ((B.γ₀.g y w : D.host.K) : D.host.E))
        rw [hG', hG'] at e1
        rw [← B.γ₀.isom x y, map_sum, map_sum]
        simp only [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.emb_conj]
        exact e1 }
  refine ⟨γ, ⟨fun x hx => GlobalTheory.T.fourfoldLattice_isometry_denominator_coprime D cc δ B hcc q hqc u h1 h2 G hG' x hx,
    fun v hv => GlobalTheory.T.inverseIsometry_fourfoldLattice_denominator_coprime_alt D cc δ B hcc hδ q hqc u hu h1 h2 h3 G hG' v hv⟩, ?_⟩
  have hd : γ.detRel B.γ₀ = LinearMap.det (G : (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)) := by
    have e : (B.γ₀.g.symm.trans γ.g) = G := by
      apply LinearEquiv.ext; intro v
      show G (B.γ₀.g (B.γ₀.g.symm v)) = G v
      rw [LinearEquiv.apply_symm_apply]
    unfold IsoK.detRel
    rw [e]
  rw [hdet, hd]
  rfl

end GlobalTheory.KapIsom
end
end

