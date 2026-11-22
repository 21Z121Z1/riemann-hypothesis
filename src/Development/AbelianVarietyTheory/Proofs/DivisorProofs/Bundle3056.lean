import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2986
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFiniteInjectiveCompleteNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1600000 in

theorem UMem.exists_baseChange : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → IsCN V' → Function.Injective io → io.Finite → ∃ (D' : DegData V' (maximalIdeal V')) (e₈' : (Fin 8 → X) ≃+ D'.toPre.X) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G') (ψ : A'.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (spMap io)).obj 𝔪.G), IsSemiAbelian G' ∧ IsGrpPullback A'.A 𝔪.A.A (spMap f) ψ ∧ (∃ w : LB.Iso A'.L (𝔪.A.L.pull ψ), w.IsGen) ∧ IsMonHom bc.hom ∧ IsPullUnif io hD bc 𝔪.U U' ∧ (∀ mu, hD.xe (e₈' mu) = 𝔪.e₈ mu) ∧ U'.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst G'.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) ∧ (∀ E : EndU 𝔪.U.toUnifPre, ∃ E' : EndU U'.toUnifPre, E'.aA.left ≫ ψ = ψ ≫ E.aA.left ∧ ∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ)) ∧ ∀ mu, ∃ u : V'ˣ, Formalism.L2.Pj.PsiCoord D'.toPre (e₈' mu) (u * mono W (fun k => io (t k)) δ mu) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 V' _ _ _ io f hf hcn hinj hfin
  have hV := 𝔪.cn
  have aR : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have aR' : AdmBase V' (maximalIdeal V') := ⟨hcn.1, inferInstance, hcn.2.1, hcn.2.2.1⟩
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := by
    letI := io.toAlgebra
    haveI : Algebra.IsIntegral V V' := ⟨hfin.to_isIntegral⟩
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V) (maximalIdeal V')
    rw [Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  let G' : Over (Sp V') := (Over.pullback (spMap io)).obj 𝔪.G
  let bc : G' ≅ (Over.pullback (spMap io)).obj 𝔪.G := Iso.refl _
  have mbc : IsMonHom bc.hom := inferInstanceAs (IsMonHom (𝟙 G'))
  have semi' : IsSemiAbelian G' := IsSemiAbelian.pullback (spMap io) 𝔪.G 𝔪.semi
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap f) 𝔪.A
  have gpA : IsGrpPullback A'.A 𝔪.A.A (spMap f) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have sq : spMap f ≫ jK V = jK V' ≫ spMap io :=
    (spMap_comp _ f).symm.trans ((congrArg spMap (RingHom.ext hf)).trans (spMap_comp io _))
  have gpG : IsGrpPullback 𝔪.A.A 𝔪.G (jK V) (𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V)) := by
    have := 𝔪.U.gen_hom
    have : IsMonHom 𝔪.U.gen.symm.hom := by show IsMonHom 𝔪.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso 𝔪.U.gen.symm).comp (isGrpPullback_pullback 𝔪.G (jK V))).congr
      (Category.id_comp _) rfl
  have gp' : IsGrpPullback ((Over.pullback (jK V')).obj G') 𝔪.G (spMap f ≫ jK V)
      (pullback.fst G'.hom (jK V') ≫ pullback.fst 𝔪.G.hom (spMap io)) :=
    ((isGrpPullback_pullback G' (jK V')).comp (isGrpPullback_pullback 𝔪.G (spMap io))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have := 𝔪.U.gen_hom

  have hgi : 𝔪.U.gen.inv.left ≫ 𝔪.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc0 : bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io) = pullback.fst 𝔪.G.hom (spMap io) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (𝔪.U.LG.L.pull (pullback.fst G'.hom (jK V') ≫
      bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB 𝔪.A.isLB gA) eA.hom.left)
      (pull_isLB 𝔪.U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (𝔪.A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ 𝔪.U.gen.inv.left)
      (chartPullLinComb 𝔪.A.L gA (fun _ => eA.hom.left) (fun _ => 𝔪.U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame 𝔪.U.LG.L _ (fun _ => pullback.fst 𝔪.G.hom (jK V)) _ _ fun _ => ?_) 𝔪.U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc0, ← heA]; simp only [Category.assoc]
  have hbc : IsGrpPullback G' 𝔪.G (specOf io) (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)) :=
    (isGrpPullback_pullback 𝔪.G (specOf io)).congr rfl hbc0.symm
  have he := GlobalTheory.PolBaseChange.eSec_comm hbc
  let L' : RigLB G' := ⟨𝔪.U.LG.L.pull (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)),
    rigPullOf (G' := G') (G := 𝔪.G) (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)) (specOf io) he 𝔪.U.LG.L 𝔪.U.LG.rig,
    pull_isLB 𝔪.U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := 𝔪.G) (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)) (specOf io) he
      𝔪.U.LG.L 𝔪.U.LG.rig 𝔪.U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf io) 𝔪.G G' _ he 𝔪.U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB 𝔪.U.LG.isLB _))
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists V _ aR 𝔪.D
  have hgen : (specOf io).base (genericPoint (Spec (CommRingCat.of V'))) ∈ Wo := by
    have : (specOf io).base (genericPoint (Spec (CommRingCat.of V'))) = genericPoint (Spec (CommRingCat.of V)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective io hinj)
    rw [this]; exact hWo
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds V V' _ _ aR aR' io hI 𝔪.D 𝔪.A 𝔪.G
    𝔪.semi 𝔪.U Wo hψ hgen G' bc mbc A' dA eA mE wA L' wL he gL rL
  have hgc : U'.gen.hom.left ≫ gA ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
      pullback.fst G'.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) := by
    rw [hgenU, hbc0, heA]
  refine ⟨D', 𝔪.e₈.trans hD.xe.symm, G', inferInstance, inferInstance, A', U', gA, hD, bc, semi', gpA,
    LBIso.symm tA, mbc, hPU, fun mu => hD.xe.apply_symm_apply _, hgc, fun E => ?_, fun mu => ?_⟩
  · have := E.homG
    have := E.homA
    have := U'.gen_hom
    let aG' : G' ⟶ G' := (Over.pullback (spMap io)).map E.aG
    have maG : IsMonHom aG' := inferInstanceAs (IsMonHom ((Over.pullback (spMap io)).map E.aG))
    have mi : IsMonHom U'.gen.inv := by infer_instance
    let aA' : A'.A ⟶ A'.A := U'.gen.inv ≫ (Over.pullback (jK V')).map aG' ≫ U'.gen.hom
    have maA : IsMonHom aA' := by infer_instance
    have hext : (Over.pullback (jK V')).map aG' ≫ U'.gen.hom = U'.gen.hom ≫ aA' := by
      simp only [aA', Iso.hom_inv_id_assoc]
    obtain ⟨E', hG', hA'⟩ := exists_degenerationEndomorphism_of_admissibleBase V' _ aR' D' A' G' semi' U' aG' aA' maG maA hext
    have hfa : aG'.left ≫ pullback.fst 𝔪.G.hom (spMap io) = pullback.fst 𝔪.G.hom (spMap io) ≫ E.aG.left :=
      pullback.lift_fst _ _ _
    have hgG : E'.aG.left ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) =
        bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) ≫ E.aG.left := by
      rw [hG', hbc0]; exact hfa
    refine ⟨E', ?_, GlobalTheory.T.pullbackUniformisation_characterMap_conjugate V V' _ _ aR aR' io hinj hI 𝔪.D D' hD 𝔪.A A' 𝔪.G G' 𝔪.semi semi' 𝔪.U U' bc mbc hPU E E' hgG⟩
    have actA : E.aA.left ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) ≫ E.aG.left := by
      have e : E.aA ≫ 𝔪.U.gen.inv = 𝔪.U.gen.inv ≫ (Over.pullback (jK V)).map E.aG := by
        rw [Iso.comp_inv_eq, Category.assoc]
        exact ((Iso.inv_comp_eq _).2 E.ext).symm
      rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _)
    have hfa' : ((Over.pullback (jK V')).map aG').left ≫ pullback.fst G'.hom (jK V') =
        pullback.fst G'.hom (jK V') ≫ aG'.left := pullback.lift_fst _ _ _
    have hgc' : U'.gen.inv.left ≫ pullback.fst G'.hom (jK V') ≫ pullback.fst 𝔪.G.hom (spMap io) =
        gA ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) := by
      have hi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
      have := hgc
      rw [hbc0] at this
      rw [← this, ← Category.assoc, hi, Category.id_comp]
    rw [hA']
    apply gpG.1.hom_ext
    · simp only [aA', Over.comp_left, Category.assoc]
      rw [hgc, hbc0, ← Category.assoc ((Over.pullback (jK V')).map aG').left, hfa', Category.assoc, hfa, actA]
      simpa only [Category.assoc] using congrArg (· ≫ E.aG.left) hgc'
    · simp only [aA', Over.comp_left, Category.assoc, Over.w, Over.w_assoc, pA.w, pA.w_assoc]
  · obtain ⟨u, hu⟩ := 𝔪.psi mu
    have hx : hD.xe ((𝔪.e₈.trans hD.xe.symm) mu) = 𝔪.e₈ mu := hD.xe.apply_symm_apply _
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD _ _ (hx.symm ▸ hu)
    refine ⟨u' * Units.map io.toMonoidHom u, ?_⟩
    have hm : mono W (fun k => io (t k)) δ mu = io (mono W t δ mu) := by
      simp only [mono, map_prod, map_pow]
    rw [hm]
    have e : ((u' * Units.map io.toMonoidHom u : V'ˣ) : V') * io (mono W t δ mu) = u' * io (u * mono W t δ mu) := by
      rw [Units.val_mul, map_mul, ← _root_.mul_assoc]; rfl
    rw [e]; exact hu'

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeMapEq
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

namespace GlobalTheory.PDivDescend

section Bialg

variable {R K A B : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing A] [Bialgebra R A]
  [CommRing B] [Bialgebra R B]

theorem one_tmul_injective [Module.Flat R A] (hK : Function.Injective (algebraMap R K)) {a b : A}
    (h : (1 : K) ⊗ₜ[R] a = (1 : K) ⊗ₜ[R] b) : a = b :=
  Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := A) hK h

theorem two_injective [Module.Flat R A] (hK : Function.Injective (algebraMap R K)) :
    Function.Injective (toBaseChange R K A).two := by
  have e : ∀ c : A ⊗[R] A, (toBaseChange R K A).two c =
      TensorProduct.AlgebraTensorModule.distribBaseChange R K A A ((1 : K) ⊗ₜ[R] c) := fun c => by
    induction c with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul a b => simp
  intro x y h
  rw [e, e] at h
  exact Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := A ⊗[R] A) hK
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R K A A).injective h)

theorem exists_bialgHom [Module.Flat R A] (hK : Function.Injective (algebraMap R K))
    (f : K ⊗[R] B →ₐc[K] K ⊗[R] A)
    (hf : ∀ b : B, ∃ a : A, f ((1 : K) ⊗ₜ[R] b) = (1 : K) ⊗ₜ[R] a) :
    ∃ g : B →ₐc[R] A, ∀ b, f ((1 : K) ⊗ₜ[R] b) = (1 : K) ⊗ₜ[R] g b := by
  choose g hg using hf
  have hs : ∀ (r : R) (b : B), g (r • b) = r • g b := fun r b => one_tmul_injective hK (by
    rw [← hg, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hg, ← algebraMap_smul K r,
      ← algebraMap_smul K r, map_smul])
  have h1 : g 1 = 1 := one_tmul_injective hK ((hg 1).symm.trans (map_one f))
  let g₁ : B →+* A :=
    { toFun := g
      map_one' := h1
      map_mul' := fun a b => one_tmul_injective hK (by
        have h := map_mul f ((1 : K) ⊗ₜ[R] a) ((1 : K) ⊗ₜ[R] b)
        rw [hg a, hg b, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          _root_.mul_one, hg] at h
        exact h)
      map_zero' := by simpa using hs 0 0
      map_add' := fun a b => one_tmul_injective hK (by
        rw [← hg, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, hg, hg]) }
  let F := (SemiBialgHom.ofBialgHom f).comp (toBaseChange R K B)
  have hF : ∀ b, F b = toBaseChange R K A (g b) := hg
  let g₂ : SemiBialgHom (RingHom.id R) B A :=
    { toRingHom := g₁
      smul_map := hs
      counit_map := fun b => hK (by
        have h := F.counit_map b
        rw [hF, (toBaseChange R K A).counit_map] at h
        exact h)
      comul_map := fun b => two_injective hK (by
        rw [SemiBialgHom.two_comul]
        refine ((congrArg _ (hF b).symm).trans (F.two_comul b).symm).trans ?_
        generalize comul (R := R) b = c
        induction c with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b =>
          simp only [TensorProduct.map_tmul, SemiBialgHom.lin_apply, hF]
          rfl) }
  exact ⟨g₂.toBialgHom, hg⟩

end Bialg

theorem exists_baseChangeMap_eq (p : ℕ) (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (GG HH : PDivGroup p R) (f : GG.baseChange K ⟶ HH.baseChange K)
    (hf : ∀ (n : ℕ) (b : HH.A n), ∃ a : GG.A n, f.app n ((1 : K) ⊗ₜ[R] b) = (1 : K) ⊗ₜ[R] a) :
    ∃ φ : GG ⟶ HH, PDivGroup.baseChangeMap K φ = f := by
  have hK := IsFractionRing.injective R K
  choose g hg using fun n => exists_bialgHom (A := GG.A n) (B := HH.A n) hK (f.app n) (hf n)
  refine ⟨⟨g, fun n => BialgHom.ext fun b => one_tmul_injective hK ?_⟩,
    baseChange_hom_ext fun n b => (hg n b).symm⟩
  have h := res_app f n ((1 : K) ⊗ₜ[R] b)
  rw [hg] at h
  exact h.trans (hg n _)

end GlobalTheory.PDivDescend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep

theorem exists_centred_ext_tower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsCN V → IsLocalHom ev → RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ 𝔗.Ext ev io ev₂ := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act _ 𝔗 z₂ hz V _ _ _ ev hV hev _
  subst hz

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ := (X₁.M.stalkHom (𝔗.p z₂)).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ (𝔗.p z₂)
  letI : Algebra (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := (𝔗.X₂.M.stalkHom z₂).toAlgebra
  obtain ⟨hdom₂, hfr₂, hic₂, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i 𝔗.X₂ z₂
  haveI := 𝔗.fd
  haveI := 𝔗.gal
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.Poinc.integralClosure_galois_finite_invariants (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom (𝔗.p z₂))).toAlgebra
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hdom; haveI := hfr; haveI := hic; haveI := hdom₂; haveI := hfr₂; haveI := hic₂
  haveI : Algebra.IsInvariant (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) :=
    ⟨fun b hb => hfix b hb⟩
  haveI : Module.Finite (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfin
  haveI : Finite (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfinA
  have hcard : Nat.card (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) = Module.finrank X₁.Ω₁ 𝔗.X₂.Ω₁ := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (galRestrict (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)).toEquiv).symm

  have hn1 : IsUnit ((X₁.ρ.n : ℕ) : X₁.o₁) := by
    have hu := X₁.S.unit
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [X₁.ρ.N_eq]
      exact Dvd.dvd.mul_left (dvd_pow (dvd_pow_self _ (by have := X₁.ρ.two_le; omega)) two_ne_zero) _
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
  have hnA : IsUnit ((X₁.ρ.n : ℕ) : (X₁.M.Z.presheaf.stalk (𝔗.p z₂))) := by
    obtain ⟨u, hu⟩ := hn1
    have hm : algebraMap X₁.o₁ X₁.Ω₁ (↑u⁻¹) ∈ X₁.M.O (𝔗.p z₂) := Subalgebra.algebraMap_mem _ _
    refine IsUnit.of_mul_eq_one ((X₁.M.stalkEquiv _).symm ⟨_, hm⟩) (X₁.M.stalkHom_injective _ ?_)
    rw [map_mul, map_one, map_natCast, ← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    change ((X₁.ρ.n : ℕ) : X₁.Ω₁) * algebraMap X₁.o₁ X₁.Ω₁ (↑u⁻¹) = 1
    rw [← map_natCast (algebraMap X₁.o₁ X₁.Ω₁), ← hu, ← map_mul, Units.mul_inv, map_one]
  have hnV : IsUnit ((X₁.ρ.n : ℕ) : V) := by simpa using hnA.map ev
  have hdegV : IsUnit ((Module.finrank X₁.Ω₁ 𝔗.X₂.Ω₁ : ℕ) : V) := by
    obtain ⟨e, he⟩ := 𝔗.deg
    rw [he, Nat.cast_pow]
    exact hnV.pow e

  haveI : CharZero V := hV.2.2.2
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨K', _, _, β, hK'fd, hK'dvd, hβ⟩ := GlobalTheory.T.exists_finite_extension_degree_dvd_card_invariants (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) hinj (FractionRing V)
    ((algebraMap V (FractionRing V)).comp ev)
  haveI := hK'fd
  have hK'u : IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) := by
    rw [hcard] at hK'dvd
    obtain ⟨c, hc⟩ := hK'dvd
    rw [hc, Nat.cast_mul] at hdegV
    exact isUnit_of_mul_isUnit_left hdegV
  obtain ⟨V', _, _, _, io, j, hV', hioi, hiof, hiol, hcon, hjinj, hj, hjr⟩ := GlobalTheory.T.exists_complete_normal_integralClosure_unit_degree V hV K' hK'u
  have hβmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, β b ∈ j.range := by
    intro b
    obtain ⟨P, hPm, hP⟩ := integralClosure.isIntegral b
    obtain ⟨y, hy⟩ := hjr (β b) ⟨P.map ev, hPm.map ev, by
      rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hβ, ← Polynomial.hom_eval₂, hP, map_zero]⟩
    exact ⟨y, hy⟩
  let jr : V' ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hjinj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let β' : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* V' := jr.symm.toRingHom.comp (β.codRestrict j.range hβmem)
  have hβ' : ∀ b, j (β' b) = β b := fun b => congrArg Subtype.val (jr.apply_symm_apply ⟨β b, hβmem b⟩)

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) := (𝔗.p.stalkMap z₂).hom.toAlgebra
  have hg1 : ∀ x : (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), 𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) :=
    fun x => (GlobalTheory.T.stalkHom_stalkMap_eq_functionFieldExtension X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p 𝔗.p_pt z₂ x)
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq fun x => (hg1 x).symm
  have hinj₂ := 𝔗.X₂.M.stalkHom_injective z₂
  have hBmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, (b : 𝔗.X₂.Ω₁) ∈ (𝔗.X₂.M.stalkHom z₂).range := fun b => by
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := (𝔗.X₂.M.Z.presheaf.stalk z₂)) (K := 𝔗.X₂.Ω₁)).1
      (IsIntegral.tower_top (A := (𝔗.X₂.M.Z.presheaf.stalk z₂)) b.2)
    exact ⟨y, hy⟩
  let e₂ : (𝔗.X₂.M.Z.presheaf.stalk z₂) ≃+* (𝔗.X₂.M.stalkHom z₂).range := RingEquiv.ofBijective (𝔗.X₂.M.stalkHom z₂).rangeRestrict
    ⟨fun a b h => hinj₂ (congrArg Subtype.val h), (𝔗.X₂.M.stalkHom z₂).rangeRestrict_surjective⟩
  let f : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* (𝔗.X₂.M.Z.presheaf.stalk z₂) :=
    e₂.symm.toRingHom.comp (((integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁).val : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] 𝔗.X₂.Ω₁).toRingHom.codRestrict _ hBmem)
  have hf : ∀ b, 𝔗.X₂.M.stalkHom z₂ (f b) = b := fun b => congrArg Subtype.val (e₂.apply_symm_apply ⟨_, hBmem b⟩)
  have hfB : ∀ (t : (𝔗.X₂.M.Z.presheaf.stalk z₂)) (h : 𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁), f ⟨_, h⟩ = t :=
    fun t h => hinj₂ (hf _)
  have hloc : IsLocalHom (f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁))) := by
    have h : f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = (𝔗.p.stalkMap z₂).hom :=
      RingHom.ext fun a => hinj₂ (by rw [RingHom.comp_apply, hf, hg1]; rfl)
    rw [h]; infer_instance
  have hint : ∀ t : (𝔗.X₂.M.Z.presheaf.stalk z₂), (∃ P : Polynomial (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), P.Monic ∧ P.eval₂ (𝔗.p.stalkMap z₂).hom t = 0) →
      𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := by
    rintro t ⟨P, hPm, hP⟩
    refine ⟨P, hPm, ?_⟩
    have h : algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ = (𝔗.X₂.M.stalkHom z₂).comp (𝔗.p.stalkMap z₂).hom := RingHom.ext fun x => (hg1 x).symm
    rw [h, ← Polynomial.hom_eval₂, hP, map_zero]
  have hsurj : ∀ y : (𝔗.X₂.M.Z.presheaf.stalk z₂), ∃ b s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ y * f s = f b := by
    intro y
    obtain ⟨b, s, hs, hys, hb, hs'⟩ := GlobalTheory.T.finite_stalk_germ_quotient_integral_unit_denominator _ _ 𝔗.p 𝔗.p_fin z₂ y
    refine ⟨⟨_, hint b hb⟩, ⟨_, hint s hs'⟩, ?_, ?_⟩
    · rw [hfB]; exact hs
    · rw [hfB, hfB]; exact hys
  have hker : ∀ b, f b = 0 → ∃ s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ s * b = 0 := fun b hb =>
    ⟨1, by rw [map_one]; exact isUnit_one, by
      rw [_root_.one_mul]; exact Subtype.ext (by rw [← hf b, hb, map_zero]; rfl)⟩
  haveI := hiol; haveI := hev
  have hβ'A : β'.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = io.comp ev := RingHom.ext fun a =>
    hjinj ((hβ' _).trans ((RingHom.congr_fun hβ a).trans (RingHom.congr_fun hj (ev a)).symm))
  obtain ⟨ev₂, hev₂, hcomp⟩ := GlobalTheory.T.twisted_lift_invariantExtension_localisation (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (𝔗.X₂.M.Z.presheaf.stalk z₂)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) f hloc hsurj hker V' (io.comp ev) β' inferInstance hβ'A
  refine ⟨V', inferInstance, inferInstance, inferInstance, io, ev₂, hV', hioi, hiof, hiol, hcon, hev₂, fun x x₂ hx => ?_⟩
  have h : x₂ = f (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) x) := hinj₂ (by rw [hf]; exact hx)
  rw [h]
  exact RingHom.congr_fun hcomp x

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorRationalSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.Denom

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem exists_sec_tens {L M : LB Y} (hL : L.IsLB) (hM : M.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (u : M.Sec) (hu : genericPoint Y ∈ nonzeroLocus u)
    (hE : (divOfRatSec hL hr + divOfSec hM u hu).Eff) :
    ∃ (t : (tens L M).Sec) (ht : genericPoint Y ∈ nonzeroLocus t), ∀ i j, genericPoint Y ∈ L.U i →
      genericPoint Y ∈ M.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j := by
  have P := (presents_divOfRatSec hL hr).tens (presents_divOfRatSec hM (isRatSec_ratOfSec u hu))
  obtain ⟨t, ht⟩ := P.exists_rat_eq (f := 1) (CartierDiv.mem_sections.2 fun x => hE x)
  have hη : genericPoint Y ∈ nonzeroLocus t :=
    (P.generatesAt_rat_iff t).1 (ht ▸ CartierDiv.generatesAt_genericPoint _ one_ne_zero)
  refine ⟨t, hη, fun i j hi hj => Units.ext ?_⟩
  have e := P.rat_mul t (i, j) ⟨hi, hj⟩
  rw [ht, one_mul] at e
  rw [val_ratOfSec (show genericPoint Y ∈ (tens L M).U (i, j) from ⟨hi, hj⟩), ← e]

theorem gen_mem_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m) := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  have hj : genericPoint Y ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  refine (mem_nonzeroLocus_iff _ _ hj).2 ((unitAt_fnOf_iff hj hj _).1 (unitAt_genericPoint ?_))
  show fnOf _ hj (resG Y _ (t.f i) ^ m) ≠ 0
  rw [map_pow, fnOf_resG]
  exact pow_ne_zero _ (fnOf_sec_ne_zero ht hi)

theorem divOfSec_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) (hm : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m)) :
    divOfSec (isLB_lbPow hL m) (Cartier.secPow t m) hm = m • divOfSec hL t ht := by
  refine CartierDiv.ext_of_isEqn fun x => ?_
  obtain ⟨i, hi⟩ := exists_chart hL x
  have hj : x ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  have e : ratOfSec (Cartier.secPow t m) hm (fun _ => i) = ratOfSec t ht i ^ m := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj)]
    show fnOf _ (gen_mem hj) (resG Y _ (t.f i) ^ m) = _
    rw [map_pow, fnOf_resG]
  refine ⟨ratOfSec t ht i ^ m, ?_,
    ((presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i x hi).nsmul m⟩
  rw [← e]
  exact (presents_divOfRatSec (isLB_lbPow hL m) (isRatSec_ratOfSec _ hm)).isEqn _ x hj

theorem exists_open_regularAt {L : LB Y} (hL : L.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) :
    ∃ W : Y.Opens, genericPoint Y ∈ W ∧ ∀ x ∈ W, (divOfRatSec hL hr).RegularAt x 1 := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  obtain ⟨U, hU, a, ha⟩ := (regAt_genericPoint (r i : Y.functionField)).exists_fnOf
  refine ⟨L.U i ⊓ U, ⟨hi, hU⟩, fun x hx => ?_⟩
  refine ((presents_divOfRatSec hL hr).isEqn i x hx.1).regularAt_iff.2 ?_
  rw [one_mul, ← ha]
  exact regAt_fnOf hx.2 _ a

end GlobalTheory.MixHt.Denom

open GlobalTheory.MixHt.Denom in

theorem GlobalTheory.MixHt.exists_common_denom : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ (N : HermLB q) (r r' : N.B.ι → Y.functionFieldˣ), IsRatSec N.B r →
    IsRatSec N.B r' → ∃ (A : HermLB q) (u : A.B.Sec) (t t' : (N.tens A).B.Sec)
    (hu : genericPoint Y ∈ nonzeroLocus u) (ht : genericPoint Y ∈ nonzeroLocus t)
    (ht' : genericPoint Y ∈ nonzeroLocus t'), ∀ (i : N.B.ι) (j : A.B.ι), genericPoint Y ∈ N.B.U i →
    genericPoint Y ∈ A.B.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j ∧
      ratOfSec t' ht' (i, j) = r' i * ratOfSec u hu j := by
  intro k _ Y _ q hq N r r' hr hr'
  obtain ⟨n₀, j, hj, hjq⟩ := hq.isProjOver
  let H : HermLB q := (ProjSpace.hermitianTwistingSheaf k n₀).pull j hjq
  have hH : IsAmpleLB H.B := (isAmple_projective_O_one k n₀).pull_of_isClosedImmersion j
  haveI := hH.compactSpace
  obtain ⟨W, hW, hWr⟩ := exists_open_regularAt N.isLB hr
  obtain ⟨W', hW', hWr'⟩ := exists_open_regularAt N.isLB hr'
  obtain ⟨n, -, t, ht, hle, -⟩ :=
    hH.exists_affine_le (x := genericPoint Y) (U := W ⊓ W') ⟨hW, hW'⟩
  have hL := isLB_lbPow H.isLB n
  obtain ⟨N₁, h₁⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr x (hle hx).1
  obtain ⟨N₂, h₂⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr' x (hle hx).2
  have hu := gen_mem_secPow hL t ht (max N₁ N₂)
  have hD := divOfSec_secPow hL t ht (max N₁ N₂) hu
  obtain ⟨s, hs, e⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₁ _ (le_max_left _ _))
  obtain ⟨s', hs', e'⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr' (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₂ _ (le_max_right _ _))
  exact ⟨(H.pow n).pow (max N₁ N₂), Cartier.secPow t (max N₁ N₂), s, s', hu, hs, hs',
    fun i j hi hj => ⟨e i j hi hj, e' i j hi hj⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonGenericFibreDiagonalEndEighthPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_genericFibre_diagonalEnd_eighthPower : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R R' K : Type) [CommRing R] [CommRing R'] [Field K] (f : R →+* K) (f' : R' →+* K) (P : PolAV (Sp R)) (u : Sp R ⟶ F.X) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (P' : PolAV (Sp R')) (u' : Sp R' ⟶ F.X), IsDiagEnd F W P u ε → SharpOver F W P' u' → spMap f ≫ u = spMap f' ≫ u' → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A), IsDiagEnd F W P' u' ε' ∧ ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left) (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap f) a ∧ IsGrpPullback P₀.A P'.A (spMap f') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') ∧ ∀ E, (ε₀ E).left ≫ a = a ≫ (ε E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left := by
  first | exact @GlobalTheory.Poinc.exists_common_fibre_diagEnd | exact GlobalTheory.Poinc.exists_common_fibre_diagEnd | (intros; apply GlobalTheory.Poinc.exists_common_fibre_diagEnd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutingCoordinateDerivationsRegularFunctStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commuting_coordinate_derivations_regular_functions : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), ∃ d : Fin g → Derivation ℂ (Sec (str A) U) (Sec (str A) U), (∀ a b x, d a (d b x) = d b (d a x)) ∧ ∀ a x, ∀ z ∈ pre u.ex U, val u.ex U (d a x) z = fderiv ℂ (val u.ex U x) z (Pi.single a 1) := by
  first | exact @GlobalTheory.CechPer.exists_commuting_coordinate_derivations | exact GlobalTheory.CechPer.exists_commuting_coordinate_derivations | (intros; apply GlobalTheory.CechPer.exists_commuting_coordinate_derivations <;> assumption)
end

