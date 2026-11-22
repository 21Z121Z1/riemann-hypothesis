import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneOverLIdeleCharacterValueStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_over_l_idele_character_value : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (D : R), D ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ClearsIdem (FractionRing R) (condQ 𝔣 Q) D →
    ∃ (δ₀ : X₀.DetGen) (u₀ : R),
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        Fintype.card I • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  first | exact @GlobalTheory.LatModel.exists_detGen_wedge_val_le | exact GlobalTheory.LatModel.exists_detGen_wedge_val_le | (intros; apply GlobalTheory.LatModel.exists_detGen_wedge_val_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

variable {R : Type} [CommRing R] [IsDomain R]

theorem famMapTw_trPt (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {b b' : TF (R := R) (Kb R) ⟶ D.P.A}
    (hb : twF ρ ≫ b = b') : famMapTw D ρ ≫ DegPre.trPt D (Kb R) b = DegPre.trPt D (Kb R) b' ≫ famMapTw D ρ := by
  subst hb
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trPt]
  · simp [DegPre.trPt, padd, comp_lift_assoc]

theorem zF_famMapTw (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) :
    DegPre.zF D (Kb R) ≫ famMapTw D ρ = twF ρ ≫ DegPre.zF D (Kb R) := by
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem famMapTw_famφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) (β : D.X) (i : Fin 4) :
    (famMapTw D ρ).left ≫ DegPre.famφ D (Kb R) β i = DegPre.famφ D (Kb R) β i :=
  (famφ_famMap D (Kb R) (TwF ρ) β i).symm

theorem famMapTw_phiφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {y y₀ : D.X} (α : D.X)
    {b b₀ : TF (R := R) (Kb R) ⟶ D.P.A} (hy : y₀ = y) (hb : twF ρ ≫ b₀ = b) :
    (fun k => (famMapTw D ρ).left ≫ DegPre.phiφ D (Kb R) y₀ α b₀ k) = DegPre.phiφ D (Kb R) y α b := by
  subst hy
  funext k
  rcases k with i | i
  · exact famMapTw_famφ D ρ _ i
  · show (famMapTw D ρ).left ≫ (DegPre.trPt D (Kb R) b₀).left ≫ DegPre.famφ D (Kb R) α i =
      (DegPre.trPt D (Kb R) b).left ≫ DegPre.famφ D (Kb R) α i
    rw [← Category.assoc, ← Over.comp_left, famMapTw_trPt D ρ hb, Over.comp_left, Category.assoc,
      famMapTw_famφ]

theorem twF_left (ρ : Kb R →ₐ[FractionRing R] Kb R) : (twF ρ).left = spMap ρ.toRingHom := rfl

end GlobalTheory.Mum.Conj.PhiTw

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

theorem phiRel_famTw : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) (s s' : Fam D (Kb R) N),
    PhiRel D (Kb R) N p w s s' → PhiRel D (Kb R) N p₀ (frTw D τ h w) (famTw D N τ s) (famTw D N τ s') := by
  intro R _ _ D N τ p p₀ h w s s' H α u hu hu0
  have hL := D.P.isLB
  let e : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
  let σ : Kb R →ₐ[FractionRing R] Kb R := (e.symm : Kb R →ₐ[FractionRing R] Kb R)
  have hστ : ∀ x, σ (τ x) = x := fun x => e.symm_apply_apply x
  have hτσ : ∀ x, τ (σ x) = x := fun x => e.apply_symm_apply x
  have hb₀ : twF τ ≫ p.g.b = p₀.g.b := Over.OverMorphism.ext (by
    rw [Over.comp_left, twF_left]; exact h.2.1.symm)
  have hb : twF σ ≫ p₀.g.b = p.g.b := by
    rw [← hb₀, ← Category.assoc, twF_comp_eq_id hστ, Category.id_comp]
  have hφ := famMapTw_phiφ D σ α h.1 hb
  let u' := genCast hφ (LB.pullGen D.P.L _ _ u (famMapTw D σ).left)
  have hu' : u'.IsGen := genCast_isGen _ (DVR.pullGen_isGen _ _ _ u hu _)
  have hid : (twF σ).left ≫ spMap τ.toRingHom = 𝟙 _ := by
    rw [← twF_left, ← Over.comp_left, twF_comp_eq_id hστ]; rfl
  have hz : (DegPre.zF D (Kb R)).left ≫ (famMapTw D σ).left = (twF σ).left ≫ (DegPre.zF D (Kb R)).left := by
    rw [← Over.comp_left, zF_famMapTw, Over.comp_left]
  have hu'0 : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u' (DegPre.zF D (Kb R)).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) := corr_of_val hL fun y J hJ => by
    rw [val_pull hJ, val_genCast, val_pull hJ, Category.id_comp, hz, ← val_pull hJ, val_corr hJ hu0,
      val_mul hJ, val_mul hJ, val_corr hJ (h.2.2 α), val_pull hJ, frTw, val_genCast, val_pull hJ, hid]
  have H1 := (secRel_iff hL _ _ _ _ _ _ _ _ _ u').1 (H α u' hu' hu'0)
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e1 := H1 _ (famMapTw D τ).left y J hJ
  have hTT : (famMapTw D τ).left ≫ (famMapTw D σ).left = 𝟙 _ := by
    rw [← Over.comp_left, famMapTw_comp_eq_id D hτσ]; rfl
  rw [val_genCast, val_pull hJ, hTT] at e1
  rw [← h.1] at e1
  have hc : (famMapTw D τ).left ≫ (DegPre.trPt D (Kb R) p.g.b).left =
      (DegPre.trPt D (Kb R) p₀.g.b).left ≫ (famMapTw D τ).left := by
    rw [← Over.comp_left, famMapTw_trPt D τ hb₀, Over.comp_left]
  rw [sval_famTw _ _ _ _ _ _ hJ, sval_famTw _ _ _ _ _ _ hJ]
  simp only [Category.id_comp]
  rw [e1, hc]

end GlobalTheory.Mum.Conj.PhiTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartFirstChernFormOfWeightPowEqChernPartStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L), ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  first | exact @GlobalTheory.ChernCalc.TopPow.part_c1W_pow | exact GlobalTheory.ChernCalc.TopPow.part_c1W_pow | (intros; apply GlobalTheory.ChernCalc.TopPow.part_c1W_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelPDivisiblePropertiesExtend
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.Descent

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

theorem baseChangeMap_injective (hi : Function.Injective (algebraMap R K)) {G H : PDivGroup p R} {f g : G ⟶ H}
    (h : PDivGroup.baseChangeMap K f = PDivGroup.baseChangeMap K g) : f = g := by
  refine PDivGroup.hom_ext fun n => BialgHom.ext fun a => ?_
  have hinj : Function.Injective (fun b : G.A n => (1 : K) ⊗ₜ[R] b) := by
    have h1 : Function.Injective ((Algebra.linearMap R K).rTensor (G.A n)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hi
    intro x y hxy
    apply (TensorProduct.lid R (G.A n)).symm.injective
    apply h1
    simpa using hxy
  exact hinj (congrArg (fun u => Hom.app u n ((1 : K) ⊗ₜ[R] a)) h)

end GlobalTheory.GroupBplus.Aff.Descent

namespace GlobalTheory.GroupBplus.Aff.Descent

variable {p : ℕ} [Fact p.Prime] {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

theorem dualBaseChange_hom_naturality {G H : PDivGroup p R} (f : G ⟶ H) :
    (dualBaseChange K H).hom ≫ PDivGroup.baseChangeMap K (dualHom G H f) =
      dualHom _ _ (PDivGroup.baseChangeMap K f) ≫ (dualBaseChange K G).hom :=
  PDivGroup.hom_ext fun n => BialgHom.ext fun x => CartierDual.baseChange_map K (f.app n) x

theorem baseChangeMap_bidual_hom (G : PDivGroup p R) :
    PDivGroup.baseChangeMap K G.bidual.hom =
      (G.baseChange K).bidual.hom ≫ dualHom _ _ (dualBaseChange K G).inv ≫ (dualBaseChange K G.dual).hom := by
  refine PDivGroup.baseChange_hom_ext fun n a => ?_
  obtain ⟨b, rfl⟩ := (CartierDual.bidual R (G.A n)).surjective a
  change (1 : K) ⊗ₜ[R] (CartierDual.bidual R (G.A n)).symm (CartierDual.bidual R (G.A n) b) = _
  rw [BialgEquiv.symm_apply_apply]
  symm
  change (CartierDual.bidual K (K ⊗[R] G.A n)).symm _ = _
  refine CartierDual.eq_of_forall_apply (R := K) fun l => ?_
  rw [CartierDual.apply_bidual_symm]
  obtain ⟨y, rfl⟩ := (CartierDual.baseChange R K (G.A n)).surjective l
  change CartierDual.baseChangeHom R K (CartierDual R (G.A n)) ((1 : K) ⊗ₜ[R] CartierDual.bidual R (G.A n) b)
      ((CartierDual.baseChange R K (G.A n)).symm (CartierDual.baseChange R K (G.A n) y)) = _
  rw [BialgEquiv.symm_apply_apply]
  change (CartierDual.baseChangeLinear R K (CartierDual R (G.A n)) ((1 : K) ⊗ₜ[R] CartierDual.bidual R (G.A n) b)).ofConv y =
    (CartierDual.baseChangeLinear R K (G.A n) y).ofConv ((1 : K) ⊗ₜ[R] b)
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply] at hx hy ⊢; rw [hx, hy]
  | tmul r φ =>
    rw [CartierDual.baseChangeLinear_tmul_tmul, CartierDual.baseChangeLinear_tmul_tmul, CartierDual.bidual_apply]
    simp [mul_comm]

end GlobalTheory.GroupBplus.Aff.Descent

namespace GlobalTheory.GroupBplus.Aff.Descent

theorem descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (t₀ : SAB H (Sp K)) (GG₀ : PDivGroup p K) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀) (ε₀ : (PDivGroup.mu p K).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ → ∀ (GG : PDivGroup p R) (act : Action (𝓞 E) GG) (pol : GG ≅ GG.dual) (ε : (PDivGroup.mu p R).Tate) (τ : Dw.La →+ GG.Tate) (e : GG₀ ≅ GG.baseChange K), (∀ n, muRoot ε₀ n = algebraMap R K (muRoot ε n)) → (∀ a, (act₀ a : GG₀ ⟶ GG₀) ≫ e.hom = e.hom ≫ PDivGroup.baseChangeMap K (act a : GG ⟶ GG)) → pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom = e.hom ≫ PDivGroup.baseChangeMap K pol.hom → (∀ x, tateMap _ _ K e.hom (τ₀ x) = bcTate K (τ x)) → (∀ a, (act a : GG ⟶ GG) ≫ pol.hom = pol.hom ≫ dualHom GG GG (act (H.bar a))) ∧ GG.bidual.hom ≫ dualHom GG GG.dual pol.hom = -pol.hom ∧ (∀ n, IsPrimitiveRoot (muRoot ε n) (p ^ n)) ∧ (∀ (a : 𝓞 E) (x : Dw.La), τ (a • x) = tateMap GG GG R (act a) (τ x)) ∧ ∀ x y, pairing GG R (τ x) (tateMap GG GG.dual R pol.hom (τ y)) = ((Dw.EF x y : ℤ) : ℤ_[p]) • ε := by
  intro E _ _ _ H Dw p _ R K _ _ _ _ _ t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ h₀ GG act pol ε τ e hε hact hpol hτ
  have hi : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have bc_comp : ∀ {X Y Z : PDivGroup p R} (f : X ⟶ Y) (g : Y ⟶ Z),
      PDivGroup.baseChangeMap K (f ≫ g) = PDivGroup.baseChangeMap K f ≫ PDivGroup.baseChangeMap K g :=
    fun f g => (PDivGroup.baseChangeFunctor p R K).map_comp f g
  have bc_neg : ∀ {X Y : PDivGroup p R} (f : X ⟶ Y), PDivGroup.baseChangeMap K (-f) = -PDivGroup.baseChangeMap K f := by
    intro X Y f
    have h0 : PDivGroup.baseChangeMap K (0 : X ⟶ Y) = 0 := by
      have h := PDivGroup.baseChangeMap_add K (0 : X ⟶ Y) 0
      rw [add_zero] at h
      simpa using h
    rw [eq_neg_iff_add_eq_zero, ← PDivGroup.baseChangeMap_add, neg_add_cancel, h0]
  have hinv : ∀ a, e.inv ≫ (act₀ a : GG₀ ⟶ GG₀) = PDivGroup.baseChangeMap K (act a : GG ⟶ GG) ≫ e.inv := fun a => by
    rw [Iso.eq_comp_inv, Category.assoc, hact, Iso.inv_hom_id_assoc]
  have tate_inj : ∀ s s' : GG.Tate, bcTate K s = bcTate K s' → s = s' := fun s s' h =>
    TateOver.ext (funext fun n => AlgHom.ext fun a => hi (by
      have h1 := congrArg (fun z => z.pt n ((1 : K) ⊗ₜ[R] a)) h
      exact (_root_.one_mul _).symm.trans (h1.trans (_root_.one_mul _))))
  refine ⟨fun a => ?_, ?_, fun n => ?_, fun a x => ?_, fun x y => ?_⟩
  ·
    apply baseChangeMap_injective hi
    rw [← cancel_epi e.hom, bc_comp, bc_comp]
    calc e.hom ≫ PDivGroup.baseChangeMap K (act a : GG ⟶ GG) ≫ PDivGroup.baseChangeMap K pol.hom
        = (act₀ a : GG₀ ⟶ GG₀) ≫ e.hom ≫ PDivGroup.baseChangeMap K pol.hom := by
          rw [← Category.assoc, ← hact, Category.assoc]
      _ = (act₀ a : GG₀ ⟶ GG₀) ≫ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by rw [hpol]
      _ = pol₀.hom ≫ dualHom _ _ (act₀ (H.bar a)) ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by
          rw [← Category.assoc, h₀.adj a, Category.assoc]
      _ = pol₀.hom ≫ dualHom _ _ (e.inv ≫ (act₀ (H.bar a) : GG₀ ⟶ GG₀)) ≫ (dualBaseChange K GG).hom := by
          rw [dualHom_comp, Category.assoc]
      _ = pol₀.hom ≫ dualHom _ _ (PDivGroup.baseChangeMap K (act (H.bar a) : GG ⟶ GG) ≫ e.inv) ≫
            (dualBaseChange K GG).hom := by rw [hinv]
      _ = pol₀.hom ≫ dualHom _ _ e.inv ≫ dualHom _ _ (PDivGroup.baseChangeMap K (act (H.bar a) : GG ⟶ GG)) ≫
            (dualBaseChange K GG).hom := by rw [dualHom_comp, Category.assoc]
      _ = pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom ≫
            PDivGroup.baseChangeMap K (dualHom GG GG (act (H.bar a))) := by rw [dualBaseChange_hom_naturality]
      _ = e.hom ≫ PDivGroup.baseChangeMap K pol.hom ≫ PDivGroup.baseChangeMap K (dualHom GG GG (act (H.bar a))) := by
          rw [← Category.assoc e.hom, ← hpol]; simp only [Category.assoc]
  ·
    apply baseChangeMap_injective hi
    have hp' : PDivGroup.baseChangeMap K pol.hom ≫ (dualBaseChange K GG).inv = e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv := by
      rw [← cancel_epi e.hom, ← Category.assoc, ← hpol]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
    rw [← cancel_epi e.hom, bc_comp, bc_neg, Preadditive.comp_neg, ← hpol]
    calc e.hom ≫ PDivGroup.baseChangeMap K GG.bidual.hom ≫ PDivGroup.baseChangeMap K (dualHom GG GG.dual pol.hom)
        = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (dualBaseChange K GG).inv ≫
            (dualBaseChange K GG.dual).hom ≫ PDivGroup.baseChangeMap K (dualHom GG GG.dual pol.hom) := by
          rw [baseChangeMap_bidual_hom]; simp only [Category.assoc]
      _ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (dualBaseChange K GG).inv ≫
            dualHom _ _ (PDivGroup.baseChangeMap K pol.hom) ≫ (dualBaseChange K GG).hom := by
          rw [dualBaseChange_hom_naturality]
      _ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫
            dualHom _ _ (PDivGroup.baseChangeMap K pol.hom ≫ (dualBaseChange K GG).inv) ≫ (dualBaseChange K GG).hom := by
          rw [dualHom_comp, Category.assoc]
      _ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv) ≫
            (dualBaseChange K GG).hom := by rw [hp']
      _ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (dualHom _ _ e.inv) ≫ dualHom _ _ pol₀.hom ≫
            dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by
          rw [dualHom_comp, dualHom_comp]; simp only [Category.assoc]
      _ = GG₀.bidual.hom ≫ dualHom _ _ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by
          rw [← Category.assoc (PDivGroup.bidual _).hom, bidual_hom_dualHom_dualHom]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = -pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by
          rw [← Category.assoc, h₀.skew, Preadditive.neg_comp]
  ·
    exact (IsPrimitiveRoot.map_iff_of_injective hi).1 (by rw [← hε]; exact h₀.prim n)
  ·
    apply tate_inj
    rw [← hτ, h₀.lin, ← tateMap_comp, hact, tateMap_comp, hτ, tateMap_bcTate]
  ·
    refine muRoot_ext fun n => hi ?_
    rw [← muRoot_pairing_bc, muRoot_smul, map_pow, ← hε, ← muRoot_smul, ← h₀.pair, ← hτ, pairing_tateMap]
    congr 2
    have h1 : tateMap _ _ K (dualBaseChange K GG).hom (bcChar K (tateMap GG GG.dual R pol.hom (τ y))) =
        tateMap _ _ K (dualBaseChange K GG).hom (tateMap _ _ K (pol₀.hom ≫ dualHom _ _ e.inv) (τ₀ y)) := by
      rw [tateMap_dualBaseChange, ← tateMap_bcTate, ← hτ, ← tateMap_comp, ← tateMap_comp, Category.assoc, hpol]
    have h2 := congrArg (tateMap _ _ K (dualBaseChange K GG).inv) h1
    rw [← tateMap_comp, ← tateMap_comp, Iso.hom_inv_id, tateMap_id, tateMap_id] at h2
    rw [h2, ← tateMap_comp, Category.assoc, ← dualHom_comp, Iso.hom_inv_id, dualHom_id, Category.comp_id]

end GlobalTheory.GroupBplus.Aff.Descent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodScalarCoordinatesSymmBimultUpToUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodScalarCoordinates_symm_bimult_up_to_units : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) ∧ ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b) := by
  first | exact @GlobalTheory.Mum.TensPolRel.tauCoord_rel | exact GlobalTheory.Mum.TensPolRel.tauCoord_rel | (intros; apply GlobalTheory.Mum.TensPolRel.tauCoord_rel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariableStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareClass_additive_in_dual_variable : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P) (Y : Over (Sp K)) (a : Y ⟶ A.X) (b b' : Y ⟶ A'.X), AbDual.evc hP.isLB a (b * b') = AbDual.evc hP.isLB a b + AbDual.evc hP.isLB a b' := by
  first | (exact @GlobalTheory.AbDual.poincare_evc_mul_right) | (exact GlobalTheory.AbDual.poincare_evc_mul_right) | (intros; apply GlobalTheory.AbDual.poincare_evc_mul_right  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCrystalPairingSwapEqNegFlipStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareCrystalPairing_swap_eq_neg_flip : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → AbDual.IsCorrForm (dp0 R) (𝟙 _) B A (AbDual.swap P) (-φ.flip) := by
  first | exact @GlobalTheory.pairing_swap_eq_neg_flip | exact GlobalTheory.pairing_swap_eq_neg_flip | (intros; apply GlobalTheory.pairing_swap_eq_neg_flip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleOnCoverExtendsUpToCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwise_cocycle_on_cover_extends_up_to_coboundary : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u → ∃ u' : Fn1 X, IsCoc (whole X) u' ∧ Cohom W u u' := by
  first | exact @GlobalTheory.PtExt.CocExt.cocycle_extends | exact GlobalTheory.PtExt.CocExt.cocycle_extends | (intros; apply GlobalTheory.PtExt.CocExt.cocycle_extends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseOfTateValueBoundStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwise_of_tate_value_bound : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt → PtSt := by
  first | exact @GlobalTheory.FlatModel.ptSt_of_steps | exact GlobalTheory.FlatModel.ptSt_of_steps | (intros; apply GlobalTheory.FlatModel.ptSt_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDet
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.PolDet

theorem det_sum_smul_eq {D : ℕ} (x : Fin D → ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    (∑ i, x i • H i).det =
      ∑ m : Fin D → Fin D, (∏ l, x (m l)) * (Matrix.of fun j l => H (m l) j l).det := by
  simp only [Matrix.det_apply', Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  simp_rw [Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem coeff_eq {D : ℕ} (m : Fin D → Fin D) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * ∏ l, (if m l ∈ S then (-1 : ℂ) else 0) =
      if Function.Surjective m then 1 else 0 := by
  classical
  set T := Finset.univ.image m with hT
  have h1 : ∀ S : Finset (Fin D), ∏ l, (if m l ∈ S then (-1 : ℂ) else 0) =
      (-1 : ℂ) ^ D * ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0) := by
    intro S
    rw [Finset.prod_ite_zero, Finset.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_ite, mul_one,
      mul_zero, Finset.mem_sdiff, Finset.mem_univ, true_and, hT, Finset.mem_image]
    congr 1
    apply propext
    constructor
    · rintro h i hi ⟨l, rfl⟩
      exact hi (h l trivial)
    · intro h l _
      by_contra hl
      exact h (m l) hl ⟨l, rfl⟩
  have h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card *
      ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0) =
      ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) := by
    rw [Finset.prod_add, Finset.powerset_univ]
    simp [Finset.prod_const]
  have h3 : ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) =
      if Function.Surjective m then (-1 : ℂ) ^ D else 0 := by
    have : ∀ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) = if i ∈ T then (-1 : ℂ) else 0 := by
      intro i; by_cases hi : i ∈ T <;> simp [hi]
    simp_rw [this]
    rw [Finset.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ, true_implies,
      hT, Finset.mem_image, true_and]
    exact if_congr Iff.rfl rfl rfl
  simp_rw [h1, mul_left_comm _ ((-1 : ℂ) ^ D), ← Finset.mul_sum, h2, h3]
  split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]

theorem polarisation_det (D : ℕ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det =
      ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := by
  classical
  simp_rw [det_sum_smul_eq, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, coeff_eq, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij (fun τ : Equiv.Perm (Fin D) => (τ : Fin D → Fin D)) ?_ ?_ ?_ ?_
  · intro τ _
    simpa using τ.surjective
  · intro τ _ σ _ h
    exact DFunLike.coe_injective h
  · intro m hm
    have hs : Function.Surjective m := by simpa using hm
    exact ⟨Equiv.ofBijective m ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, by simp, rfl⟩
  · intro τ _
    rfl

end GlobalTheory.PolDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianVarietyDescendsOfRationalThetaPoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianVariety_descends_of_rational_thetaPoints : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n : ℕ), n.Prime → Odd n → (∀ j : ℕ, 1 ≤ j → ∃ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ IsThetaPt A (n ^ j) x fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (A₀ : PolAV (Sp F)) (a : A.A.left ⟶ A₀.A.left), IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  first | exact @GlobalTheory.ThetaDescent.descends | exact GlobalTheory.ThetaDescent.descends | (intros; apply GlobalTheory.ThetaDescent.descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationTensorPowerMonomialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedDegeneration_tensorPower_monomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsTens Q D' W pr xe → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ β' : Fin m → LinearMap.BilinForm ℤ D'.X, IsMonomial D' t β' ∧ (∀ i y z, β' i y z = β' i z y) ∧ ∀ y, y ≠ 0 → ∃ i, 0 < β' i y y := by
  first | exact @GlobalTheory.TensMono.main | exact GlobalTheory.TensMono.main | (intros; apply GlobalTheory.TensMono.main <;> assumption)
end

