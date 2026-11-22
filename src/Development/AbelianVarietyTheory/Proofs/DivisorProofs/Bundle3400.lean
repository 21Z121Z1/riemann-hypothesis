import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfFibres

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageQuotientFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.AffinePreimageFibre

theorem isPullback_comp_mono {C : Type*} [Category C] {A B T : C} (f : A ⟶ B) (c : B ⟶ T) [Mono c] :
    IsPullback f (𝟙 A) c (f ≫ c) :=
  IsPullback.of_isLimit' ⟨by simp⟩
    (PullbackCone.IsLimit.mk _ (fun s => s.snd)
      (fun s => by
        rw [← cancel_mono c]
        simp only [Category.assoc]
        exact s.condition.symm)
      (fun s => by simp)
      (fun s m _ h2 => by simpa using h2))

theorem isAffineOpen_preimage_fibre : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), IsPullback ι q p (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ W : Z.Opens, IsAffineOpen W → W ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (ι ⁻¹ᵁ W) := by
  intro X Z p U m A q ι H W hW hWU
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  let h : (W : Scheme) ⟶ Sp Γ(X, U.1) := p.resLE U.1 W hWU ≫ U.2.isoSpec.hom
  have hh : W.ι ≫ p = h ≫ chart U := by
    simp [h, chart, IsAffineOpen.fromSpec]
  have big := (isPullback_morphismRestrict ι W).paste_vert H
  rw [hh] at big
  have comm : (ι ∣_ W) ≫ h = ((ι ⁻¹ᵁ W).ι ≫ q) ≫ spMap (Ideal.Quotient.mk m) := by
    rw [← cancel_mono (chart U)]
    simpa [Category.assoc] using big.w
  have sq : IsPullback (ι ∣_ W) ((ι ⁻¹ᵁ W).ι ≫ q) h (spMap (Ideal.Quotient.mk m)) :=
    IsPullback.of_bot (v₂₁ := 𝟙 _) (by simpa using big) comm (isPullback_comp_mono _ _)
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk m)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsAffineHom (ι ∣_ W) := MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip inferInstance
  haveI : IsAffine (W : Scheme) := hW
  exact isAffine_of_isAffineHom (ι ∣_ W)

end GlobalTheory.AffinePreimageFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonGenericFibreOfMaximalAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem isClosed_singleton_of_maximal {X : Scheme.{0}} [JacobsonSpace X] (U : X.affineOpens)
    (mm : Ideal Γ(X, U.1)) (hm : mm.IsMaximal) (y : X) (hy : y ∈ U.1)
    (h : ∀ f ∈ mm, y ∉ X.basicOpen f) : IsClosed ({y} : Set X) := by
  have hU : IsAffineOpen U.1 := U.2
  set p := hU.primeIdealOf ⟨y, hy⟩ with hp
  have hpy : hU.fromSpec p = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  have hle : mm ≤ p.asIdeal := by
    intro f hf
    by_contra hfp
    apply h f hf
    have h1 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hfp
    rw [← hpy]; exact h1
  have heq : mm = p.asIdeal := hm.eq_of_le p.isPrime.ne_top hle
  have hcl : IsClosed ({p} : Set (PrimeSpectrum Γ(X, U.1))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 (heq ▸ hm)
  have he := hU.fromSpec.isOpenEmbedding
  have hlc := IsLocallyClosed.image (f := hU.fromSpec) (s := {p}) hcl.isLocallyClosed he.isInducing
    he.isOpen_range.isLocallyClosed
  have e : hU.fromSpec '' {p} = {y} := Set.image_singleton.trans (congrArg _ hpy)
  exact isClosed_singleton_of_isLocallyClosed_singleton (e ▸ hlc)

theorem isClosed_singleton_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (mm : Ideal Γ(Y.X, U.1)), mm.IsMaximal → ∀ x : gen Y, genι Y x ∈ U.1 → (∀ f ∈ mm, genι Y x ∉ Y.X.basicOpen f) → IsClosed ({x} : Set (gen Y)) := by
  intro E _ _ _ H Dw l Xo c Y U mm hm x hx h
  have : LocallyOfFiniteType Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    have := isProper_str c.F N
    rw [← hs]; infer_instance
  have : JacobsonSpace (Sp c.F) := inferInstanceAs (JacobsonSpace (PrimeSpectrum c.F))
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace Y.s
  have hc := isClosed_singleton_of_maximal U mm hm _ hx h
  have hiso : IsIso (genι Y) := isIso_fst Y
  have hinj : Function.Injective (genι Y) := (genι Y).isOpenEmbedding.injective
  have := hc.preimage (genι Y).continuous
  rwa [← Set.image_singleton, Set.preimage_image_eq _ hinj] at this

end GlobalTheory.LocReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvariantFieldDualNumberOfIsInvariantTangentVe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDerBridge

theorem valR_add_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f + g) = valR a O f + valR a O g := by
  simp only [valR, dif_pos ha, map_add]

theorem valR_mul_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f * g) = valR a O f * valR a O g := by
  simp only [valR, dif_pos ha, map_mul]

theorem isInvDer_of_isInv : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (v : TanM (𝟙 (Sp K)) A) (u : epsR K ⟶ A) (dd : Fld A.left), u.left = (tv v).left → IsTangent u → IsInv A v dd → GlobalTheory.KS.IsInvDer u dd := by
  intro K _ A _ _ v u dd hu ht hd W f
  have hpre : ((fst (epsR K) A ≫ u) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W :=
    GlobalTheory.InvFieldBasis.preimage_translate ht W
  refine GlobalTheory.LogKSBal.ext_valR _ _ fun B _ x hx => ?_
  obtain ⟨β, hβ⟩ : ∃ β : DualNumber K →+* B, x ≫ (fst (epsR K) A).left = spMap β :=
    ⟨(Spec.preimage (x ≫ (fst (epsR K) A).left)).hom, (Spec.map_preimage _).symm⟩
  letI : Algebra K B := (β.comp (algebraMap K (DualNumber K))).toAlgebra
  set e : B := β DualNumber.eps with he_def
  have he : e * e = 0 := by rw [he_def, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  let βa : DualNumber K →ₐ[K] B := { β with commutes' := fun _ => rfl }
  have hβe : βa = GlobalTheory.SqZero.epsTo K e he := DualNumber.algHom_ext (by simp [βa, e])
  have hxw : x ≫ (epsR K ⊗ A).hom = (Chart.sp (R₀ := K) B).hom := by
    rw [← Over.w (fst (epsR K) A), ← Category.assoc, hβ]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let xt : Chart.sp (R₀ := K) B ⟶ epsR K ⊗ A := Over.homMk x hxw
  let z : Chart.sp (R₀ := K) B ⟶ A := xt ≫ snd (epsR K) A
  have hfst : xt ≫ fst (epsR K) A = Chart.spMap (GlobalTheory.SqZero.epsTo K e he) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Chart.spMap_left, ← hβe]
    exact hβ
  have hmu : x ≫ ((fst (epsR K) A ≫ u) * snd (epsR K) A).left =
      ((Chart.spMap (GlobalTheory.SqZero.epsTo K e he) ≫ u : Chart.sp (R₀ := K) B ⟶ A) * z).left := by
    rw [← hfst, Category.assoc, ← MonObj.comp_mul]
    rfl
  have hz : ⊤ ≤ z.left ⁻¹ᵁ W := fun p hp => hx hp
  obtain ⟨-, H⟩ := GlobalTheory.Heat.DlogIndep.valR_translate hu ht hd e he z W hz
  rw [GlobalTheory.LogKSBal.valR_pbT x _ hpre.ge hx, hmu, H, valR_add_of x hx, valR_mul_of x hx,
    GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx, GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx,
    GlobalTheory.LogKSBal.valR_constFn _ x hx hβ]
  rfl

end GlobalTheory.InvDerBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerAffineChartOfBasicOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  first | exact @GlobalTheory.KSChartRes.isKS_top_of_basicOpen | exact GlobalTheory.KSChartRes.isKS_top_of_basicOpen | (intros; apply GlobalTheory.KSChartRes.isKS_top_of_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerOfCohomologousCocycle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSCoh

open GlobalTheory.LogKSLin
open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res le_preimage_mono)

theorem isKS_of_cohomologous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (a : ∀ i, Γ(t.G.left, W i)ˣ) (u : ∀ i i', Γ(t.G.left, W i ⊓ W i')ˣ), ⨆ i, W i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V) → (∀ i, IsField (W i) (d i)) → (∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r)) → (∀ i i', (u i i').val * resG t.G.left (inf_le_right : W i ⊓ W i' ≤ W i') (a i').val = resG t.G.left (inf_le_left : W i ⊓ W i' ≤ W i) (a i).val * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) → (∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ b, IsTranslate t φ g₀ (v b) (w b)) → valR g₀ O (d i O f - d i' O f) = ∑ b, ∑ b', φ (Θ b b') * ((valR (w b') (W i ⊓ W i') (u i i').val).snd * valR g₀ (W i ⊓ W i') (u i i')⁻¹.val) * (valR (w b) O f).snd) → IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U n v hv D Θ J W j d hj α u hcov hF hD hu hc
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup W i).trans (hcov.le.trans (t.G.hom.preimage_mono inf_le_left))
  choose dd hdF hd0 hdv using fun b => exists_invField U (hv b)
  let cf : ∀ i, Fin n → Γ(t.G.left, W i) := fun i a => -∑ b, (t.G.hom.appLE U.1 (W i) (hWU i)).hom (Θ a b) *
    (dd b (W i) (α i).val * (α i)⁻¹.val)
  refine ⟨J, W, j, fun i O f => d i O f + ∑ a, smulFld (cf i a) (dd a) O f, hcov, hj,
    fun i => isField_add (hF i) (isField_sum fun a => isField_smul _ (isField_mono (hWU i) (hdF a))),
    fun i h s => ?_, fun i i' O hO f S _ φ g w hg hgO hw => ?_⟩
  · beta_reduce
    simp only [smulFld_of_le le_rfl, hd0, mul_zero, Finset.sum_const_zero, add_zero]
    exact hD i h s
  · have hi : O ≤ W i := hO.trans inf_le_left
    have hi' : O ≤ W i' := hO.trans inf_le_right
    have hred := fun b => translate_red (hv b) hg (hw b)
    have hcf : ∀ r, O ≤ W r → valR g O (∑ a, smulFld (cf r a) (dd a) O f) = ∑ a, -∑ b, φ (Θ a b) *
        ((valR (w b) (W r) (α r).val).snd * valR g (W r) (α r)⁻¹.val) * (valR (w a) O f).snd := by
      intro r hr
      have hgr := le_preimage_mono g hr hgO
      rw [valR_eq _ _ hgO, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← valR_eq _ _ hgO, smulFld_of_le hr, valR_mul _ _ hgO, valR_res _ hr hgO,
        hdv a O (hr.trans (hWU r)) f S φ g (w a) hg hgO (hw a), valR_eq _ _ hgr, map_neg, map_sum, neg_mul,
        Finset.sum_mul]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun b _ => ?_)
      rw [← valR_eq _ _ hgr, valR_mul _ _ hgr, valR_mul _ _ hgr, valR_base U _ hg hgr,
        hdv b _ (hWU r) _ S φ g (w b) hg hgr (hw b)]
    have hgii : ⊤ ≤ g ⁻¹ᵁ (W i ⊓ W i') := le_preimage_mono g hO hgO
    have hLL : W i ⊓ W i' ≤ t.PP.L.U (j i) ⊓ t.PP.L.U (j i') := inf_le_inf (hj i) (hj i')
    have e : ∀ b, (valR (w b) _ (u i i').val).snd * valR g _ (u i i')⁻¹.val =
        (valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g _ (t.PP.L.g (j i) (j i'))⁻¹.val +
        ((valR (w b) _ (α i).val).snd * valR g _ (α i)⁻¹.val -
          (valR (w b) _ (α i').val).snd * valR g _ (α i')⁻¹.val) := by
      intro b
      have hwb := GlobalTheory.CechKS.le_preimage_of_red (hred b) hgii
      have h0 := congrArg (valR (w b) (W i ⊓ W i')) (hu i i')
      rw [valR_mul _ _ hwb, valR_mul _ _ hwb] at h0
      erw [valR_res _ _ hwb, valR_res _ _ hwb, valR_res _ _ hwb] at h0
      refine GlobalTheory.CechKS.dlog_of_mul_eq _ _ _ _ _ _ _ _ (by rw [h0])
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) (le_preimage_mono g hi hgO) (α i))
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) (le_preimage_mono g hi' hgO) (α i'))
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) (le_preimage_mono g hLL hgii) _)
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) hgii (u i i'))
    beta_reduce
    rw [show d i O f + ∑ a, smulFld (cf i a) (dd a) O f - (d i' O f + ∑ a, smulFld (cf i' a) (dd a) O f) =
        (d i O f - d i' O f) + ∑ a, smulFld (cf i a) (dd a) O f - ∑ a, smulFld (cf i' a) (dd a) O f by ring,
      GlobalTheory.CechInv.valR_sub _ _ hgO, valR_add _ _ hgO, hc i i' O hO f S φ g w hg hgO hw, hcf i hi, hcf i' hi']
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    linear_combination (φ (Θ a b) * (valR (w a) O f).snd) * e b

end GlobalTheory.LogKSCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section
namespace GlobalTheory.VertCoeffRing

theorem isLieBasis_tvE : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  intro R _ G _ _ n v
  have hE : (overAt (𝟙 (Sp R)) (DualNumber R)).hom = (epsR R).hom := by
    simp [epsR, overAt]
  let e : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (𝟙 _) (by simp [hE])
  let f : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ epsR R := Over.homMk (𝟙 _) (by simp [hE])
  have hfe : f ≫ e = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])
  have hef : e ≫ f = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])

  have htv : ∀ x : TanM (𝟙 (Sp R)) G, tvE x = e ≫ tv x := by
    intro x
    apply Over.OverMorphism.ext
    first
    | (simp only [e, Over.comp_left, Over.homMk_left, Category.id_comp]; exact tvE_left x)
    | simp [e, tvE_left x]
  have hadd : ∀ x y : TanM (𝟙 (Sp R)) G, tvE (x + y) = tvE x * tvE y := by
    intro x y; rw [htv, htv, htv, PullbackSections.tv_add, MonObj.comp_mul]
  have hzero : tvE (0 : TanM (𝟙 (Sp R)) G) = 1 := by
    rw [htv, PullbackSections.tv_zero, MonObj.comp_one]

  have hsmul : ∀ (a : R) (x : TanM (𝟙 (Sp R)) G),
      (tvE (a • x)).left = spMap (epsScaleR a) ≫ (tvE x).left := by
    intro a x; rw [tvE_left, tvE_left, PullbackSections.tv_smul]
    first
    | rfl
    | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
  have hinj : ∀ x y : TanM (𝟙 (Sp R)) G, tvE x = tvE y → x = y := by
    intro x y h
    apply PullbackSections.tanM_ext
    have h' := congrArg (fun t => f ≫ t) h
    simpa [htv, ← Category.assoc, hfe] using h'
  have hsum : ∀ (c : Fin n → R) (s : Finset (Fin n)),
      tvE (∑ i ∈ s, c i • v i) = ∏ i ∈ s, tvE (c i • v i) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]

  have hcomb : ∀ (c : Fin n → R) (w : epsR R ⟶ G),
      IsLieComb c (fun a => tvE (v a)) w ↔ w = tvE (∑ i, c i • v i) := by
    intro c w
    rw [IsLieComb.eq_1, hsum]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [List.prod_ofFn]
      refine Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext ?_
      rw [hu i, hsmul]
    · rintro rfl
      exact ⟨fun i => tvE (c i • v i), fun i => hsmul _ _, by rw [List.prod_ofFn]⟩

  have hfa : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp
  have hdual : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    simp only [spMap.eq_1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id]
    all_goals rfl
  have hz : spMap (epsScaleR (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have h0 : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
      refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
      all_goals first
        | (simp [epsScaleR]; done)
        | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done)
        | (simp [epsScaleR.eq_1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fstHom_apply,
            TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]; done)
        | rfl
        | (simp [epsScaleR]; rfl)
    rw [h0]
    simp only [spMap.eq_1, CommRingCat.ofHom_comp, Spec.map_comp]
  have hu : (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left = spMap (algebraMap R (DualNumber R)) := by
    first
    | simp [overAt]
    | (have h := Over.w (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))); simpa [overAt] using h)
  have hone : (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left =
      spMap (algebraMap R (DualNumber R)) ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := by
    calc (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left
        = (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := rfl
      _ = _ := by rw [hu]

  have key : ∀ g : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, smT (𝟙 (Sp R)) 0 g = 1 ↔ IsTangent (e ≫ g) := by
    intro g
    rw [IsTangent.eq_1]
    have hl : (smT (𝟙 (Sp R)) 0 g).left = spMap (algebraMap R (DualNumber R)) ≫
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g.left := by
      rw [← Category.assoc, ← hz]
      first
      | rfl
      | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
    have he : ∀ t : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (e ≫ t).left =
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t.left := by
      intro t; simp [e]
    rw [he]
    constructor
    · intro h
      have h2 := congrArg Over.Hom.left h
      rw [hl, hone] at h2
      have h3 := congrArg (fun t => spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t) h2
      simpa only [← Category.assoc, hdual, Category.id_comp] using h3
    · intro h
      apply Over.OverMorphism.ext
      rw [hl, hone, h]
  have htan : ∀ x, IsTangent (tvE x) := fun x => by
    rw [htv]; exact (key (tv x)).1 (PullbackSections.tv_mem x)
  have hsurj : ∀ w : epsR R ⟶ G, IsTangent w → ∃ x, tvE x = w := by
    intro w hw
    have hw' : IsTangent (e ≫ (f ≫ w)) := by rwa [← Category.assoc, hef, Category.id_comp]
    refine ⟨PullbackSections.mkT (f ≫ w) ((key _).2 hw'), ?_⟩
    rw [htv, PullbackSections.tv_mkT, ← Category.assoc, hef, Category.id_comp]
  rw [IsLieBasis.eq_1]
  refine ⟨fun i => htan (v i), fun w hw => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj w hw
  refine ⟨⇑(v.repr x), (hcomb _ _).2 ?_, fun c hc => ?_⟩
  · rw [v.sum_repr]
  · have h := hinj _ _ ((hcomb c _).1 hc)
    rw [h, v.repr_sum_self]

end GlobalTheory.VertCoeffRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfectPairOfGeometricFibres
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairFibres

section Algebra

open Module TensorProduct GlobalTheory.PrincipalPolPairing

variable {R Ω : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
  {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module Ω M'] [AddCommGroup N'] [Module Ω N']
  {f : M →ₛₗ[algebraMap R Ω] M'} {f' : N →ₛₗ[algebraMap R Ω] N'}

theorem subsingleton_coker₂ [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] (hf : Function.Bijective (GlobalTheory.DeRham.liftSemi f))
    (hf' : Function.Bijective (GlobalTheory.DeRham.liftSemi f')) (θ : Dual R M →ₗ[R] N)
    (φ' : Dual Ω M' →ₗ[Ω] Dual Ω (Dual Ω N')) (hφ : Function.Surjective φ')
    (h : ∀ (x : Dual R M) (y : Dual R N) (x' : Dual Ω M') (y' : Dual Ω N'),
      (∀ c, x' (f c) = algebraMap R Ω (x c)) →
      (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (y (θ x))) :
    Subsingleton (Ω ⊗[R] (N ⧸ LinearMap.range θ)) := by
  let e := LinearEquiv.ofBijective _ hf'
  haveI : Module.Finite Ω N' := Module.Finite.equiv e
  haveI : Module.Projective Ω N' := Module.Projective.of_equiv e
  let π : N' →ₗ[Ω] Ω ⊗[R] (N ⧸ LinearMap.range θ) :=
    (LinearMap.range θ).mkQ.baseChange Ω ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    (LinearMap.baseChange_surjective Ω (Submodule.mkQ_surjective _)).comp e.symm.surjective
  let θ' : Dual Ω M' →ₗ[Ω] N' := (Module.evalEquiv Ω N').symm.toLinearMap ∘ₗ φ'
  have hθ' : Function.Surjective θ' := (Module.evalEquiv Ω N').symm.surjective.comp hφ
  have k : π ∘ₗ θ' = 0 := by
    refine ext_corr hf fun x x' hx ↦ ?_
    have e₁ : θ' x' = f' (θ x) := by
      apply (Module.evalEquiv Ω N').injective
      refine ((Module.evalEquiv Ω N').apply_symm_apply _).trans (ext_corr hf' fun y y' hy ↦ ?_)
      rw [h x y x' y' hx hy, ← hy]
      rfl
    have e₂ : f' (θ x) = e (1 ⊗ₜ θ x) := (one_smul Ω (f' _)).symm
    rw [LinearMap.comp_apply, e₁, e₂]
    simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, LinearMap.baseChange_tmul,
      LinearMap.zero_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self θ x), tmul_zero]
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := (hπ.comp hθ') a
  obtain ⟨b, rfl⟩ := (hπ.comp hθ') b
  exact (LinearMap.congr_fun k a).trans (LinearMap.congr_fun k b).symm

end Algebra

open Module

theorem isPerfPair_of_fibres₂ : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] (φ : Module.Dual R M →ₗ[R] Module.Dual R N →ₗ[R] R), (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω], ∃ (M' N' : Type 1) (_ : AddCommGroup M') (_ : Module Ω M') (_ : AddCommGroup N') (_ : Module Ω N') (f : M →ₛₗ[algebraMap R Ω] M') (f' : N →ₛₗ[algebraMap R Ω] N') (φ' : Module.Dual Ω M' →ₗ[Ω] Module.Dual Ω N' →ₗ[Ω] Ω), Function.Bijective (liftSemi f) ∧ Function.Bijective (liftSemi f') ∧ φ'.IsPerfPair ∧ ∀ (x : Module.Dual R M) (x' : Module.Dual Ω M') (y : Module.Dual R N) (y' : Module.Dual Ω N'), (∀ c, x' (f c) = algebraMap R Ω (x c)) → (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (φ x y)) → φ.IsPerfPair := by
  intro R _ M N _ _ _ _ _ _ _ _ φ h
  let E := Module.evalEquiv R M
  let E' := Module.evalEquiv R N
  have ev (z : Dual R (Dual R M)) (y : Dual R M) : y (E.symm z) = z y :=
    LinearMap.congr_fun (E.apply_symm_apply z) y
  have ev' (z : Dual R (Dual R N)) (y : Dual R N) : y (E'.symm z) = z y :=
    LinearMap.congr_fun (E'.apply_symm_apply z) y
  have s₁ : Function.Surjective (E'.symm.toLinearMap ∘ₗ φ) := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine GlobalTheory.PrincipalPolPairing.subsingleton_of_fibres (R := R) fun p ↦ ?_
    obtain ⟨M', N', _, _, _, _, f, f', φ', hf, hf', hp, k⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    exact subsingleton_coker₂ hf hf' _ φ' hp.bijective_left.2 fun x y x' y' hx hy ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev', k x x' y y' hx hy]
  have s₂ : Function.Surjective (E.symm.toLinearMap ∘ₗ φ.flip) := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine GlobalTheory.PrincipalPolPairing.subsingleton_of_fibres (R := R) fun p ↦ ?_
    obtain ⟨M', N', _, _, _, _, f, f', φ', hf, hf', hp, k⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    exact subsingleton_coker₂ hf' hf _ φ'.flip hp.bijective_right.2 fun y x y' x' hy hx ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev, LinearMap.flip_apply, LinearMap.flip_apply,
        k x x' y y' hx hy]
  refine LinearMap.IsPerfPair.of_bijective _ ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · refine LinearMap.ext fun c ↦ ?_
    obtain ⟨y, rfl⟩ := s₂ c
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev, LinearMap.flip_apply, hx]
    rfl
  · obtain ⟨x, hx⟩ := s₁ (E'.symm z)
    exact ⟨x, E'.symm.injective hx⟩

end GlobalTheory.PairFibres
end
end

