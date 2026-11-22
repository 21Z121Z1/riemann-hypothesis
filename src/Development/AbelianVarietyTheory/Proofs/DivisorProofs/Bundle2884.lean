import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeClsPullHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd.GAdjFst

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem psum_comp_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f]
    {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I ≫ f = psum H (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (fun z : T ⟶ G => z ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem cubeCls_pull_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H)
    [IsMonHom f] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic H.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (pull f.left c) = GlobalTheory.ZH.EndoExtend.cubeCls H (fun i => x i ≫ f) c := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← pull_comp, ← Over.comp_left, psum_comp_hom]

theorem cubeCls_add {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G))
    (a b : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (a + b) = GlobalTheory.ZH.EndoExtend.cubeCls G x a + GlobalTheory.ZH.EndoExtend.cubeCls G x b := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  simp only [map_add, smul_add, Finset.sum_add_distrib]

theorem cubeCls_one_left {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (y : T ⟶ G) (c : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G ![1, y] c = 0 := by
  have h := GlobalTheory.ZH.CubeRootAut.cubeCls_pair (1 : T ⟶ G) y c
  have e : GlobalTheory.ZH.EndoExtend.cubeCls G ![1, y] c = GlobalTheory.TripleProd.cubeCls ![1, y] c := rfl
  rw [e, h, _root_.one_mul]
  abel

end GlobalTheory.MumProd.GAdjFst

theorem GlobalTheory.MumProd.gAdj_prod_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have e0 : GlobalTheory.CechPic.cls _ hL = GlobalTheory.CechPic.pull (fst G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₁) +
      GlobalTheory.CechPic.pull (snd G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₂) :=
    (GlobalTheory.CechPic.cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj
  refine (GlobalTheory.CechPic.cls_eq_iff _ _).1 ((GlobalTheory.ZH.EndoExtend.cls_cubeLB (G₁ ⊗ G₂) _ hL).trans
    (Eq.trans ?_ (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₁ _ hL₁).symm))
  rw [e0,
    GlobalTheory.MumProd.GAdjFst.cubeCls_add, GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom,
    GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom]
  have h₁ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ fst G₁ G₂) =
      ![fst G₁ (G₁ ⊗ G₂), snd G₁ (G₁ ⊗ G₂) ≫ fst G₁ G₂] := by
    funext i; fin_cases i <;> simp
  have h₂ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ snd G₁ G₂) =
      ![1, snd G₁ (G₁ ⊗ G₂) ≫ snd G₁ G₂] := by
    funext i; fin_cases i <;> simp
  rw [h₁, h₂, GlobalTheory.MumProd.GAdjFst.cubeCls_one_left, add_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubePointsFstEqPartialSumsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.PairPts

private theorem psum_two_01 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0, 1} = u * v := by
  have hl : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  rw [psum, hl]
  simp [padd, pzero, Hom.mul_def, Hom.one_def]

private theorem psum_two_e {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] ∅ = 1 := by
  have hl : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  rw [psum, hl]
  simp [pzero, Hom.one_def]

private theorem psum_two_0 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0} = u := by
  have hl : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  rw [psum, hl]
  have := psum_two_e G u v
  rw [psum] at this
  simp only [List.foldr_cons, List.foldr_nil, List.filter] at this ⊢
  show u * pzero G T = u
  simp [pzero, Hom.one_def] at this ⊢

private theorem psum_two_1 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {1} = v := by
  have hl : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  rw [psum, hl]
  show v * pzero G T = v
  simp [pzero, Hom.one_def]

theorem lamPts_fst_eq_psum : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (f : S₀ ⟶ S) (β : B₀.left ⟶ B.left) (β₂ : (G2 B₀).left ⟶ (G2 B).left), IsGrpPullback B₀ B f β → IsSquare β β₂ → ∀ (Y : Over S₀) (x y : Y ⟶ B₀) (x' y' : Y ⟶ (Over.pullback f).obj B), x'.left ≫ pullback.fst B.hom f = x.left ≫ β → y'.left ≫ pullback.fst B.hom f = y.left ≫ β → ∀ k : Fin 4, lamPts x' y' k ≫ pullback.fst B.hom f = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k)).left := by
  intro S₀ S B₀ _ _ B _ _ f β β₂ hβ hsq Y x y x' y' hx hy k
  have hm : ((lift x y).left ≫ β₂) ≫ (G2 B).hom = (Over.mk (Y.hom ≫ f)).hom := by
    have h1 : (G2 B).hom = (fst B B).left ≫ B.hom := (Over.w (fst B B)).symm
    rw [h1, Category.assoc, ← Category.assoc β₂, hsq.1, Category.assoc, hβ.1.w, ← Category.assoc,
      ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Category.assoc x.left, Over.w x]
    rfl
  let u : Over.mk (Y.hom ≫ f) ⟶ G2 B := Over.homMk ((lift x y).left ≫ β₂) hm
  have key : ∀ g : G2 B ⟶ B, (lift x y).left ≫ β₂ ≫ g.left = (u ≫ g).left := fun g => by
    simp [u]
  have hu1 : (u ≫ fst B B).left = x.left ≫ β := by
    rw [← key, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
  have hu2 : (u ≫ snd B B).left = y.left ≫ β := by
    rw [← key, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have h := isGrpPullback_pullback B f
  have m : (x' * y').left ≫ pullback.fst B.hom f = ((u ≫ fst B B) * (u ≫ snd B B)).left :=
    (h.2 Y x' y' _ _ (hu1.trans hx.symm) (hu2.trans hy.symm)).symm
  have o : (1 : Y ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f =
      (1 : Over.mk (Y.hom ≫ f) ⟶ B).left :=
    congrArg (fun z => z.left) (map_one (pushHom h Y))
  have hx2 : x2 B = ![fst B B, snd B B] := rfl
  fin_cases k
  · show (x' * y').left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0, 1}).left
    rw [hx2, psum_two_01, key, comp_mul, m]
  · show x'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0}).left
    rw [hx2, psum_two_0, key, hu1, hx]
  · show y'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {1}).left
    rw [hx2, psum_two_1, key, hu2, hy]
  · show (1 : Y ⟶ (Over.pullback f).obj B).left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ∅).left
    rw [hx2, psum_two_e, key, o]
    congr 1
    simp [Hom.one_def]

end GlobalTheory.PairPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalEvenCharacterLeadingTermsMemMaximalIdealStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_even_character_leading_terms_mem_maximalIdeal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ α : X, ∃ k₀ : ℕ, ∀ k ≥ k₀, (∀ m, m ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {m | ¬ ∃ s ∈ maximalIdeal R ^ n, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s}.Finite := by
  first | exact @GlobalTheory.LeadTerm.lead_mem | exact GlobalTheory.LeadTerm.lead_mem | (intros; apply GlobalTheory.LeadTerm.lead_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupPullbackCocyclesPointValueStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_pullback_cocycles_pointValue : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)).1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) = ψ (fv a E E' φ (z ≫ fst A B)) * fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
  first | exact @GlobalTheory.PtExt.cupZ_pull_apply_fv | exact GlobalTheory.PtExt.cupZ_pull_apply_fv | (intros; apply GlobalTheory.PtExt.cupZ_pull_apply_fv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLatticeSlopeSqGoodCoverLeCore
section
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC

noncomputable section

namespace GlobalTheory.CoreRing

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem slope_sq_latOver_sub_le : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (T.R j)), LawsJ T → InR D j → Y.Good e o → Dom a n → S ⊆ (T.cuspA j a n : Set (T.R j)) → GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n) → GoodW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtZ a n) → slope_sq (Y.nrm (wtZ a n)) (Y.latOver (wtZ a n) S) - 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ slope_sq (normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n)) (latW (T.U j) (wtZ a n) ⊓ ((Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype).restrictScalars (𝓞 T.Q.c.F)) := by
  intro D T j Y e o a n S hT hj hY hDom hS hG hG₂
  obtain ⟨hLc, hNc⟩ := GlobalTheory.T.principalLevelLiftModuliLaws_of_core D T j hT hj
  obtain ⟨hLd, hGal, hPull⟩ := GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW
  letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra
  obtain ⟨π, hπP, hπli, hπN, hπlat, -, hπD⟩ := GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent D j _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle (T.U j)
    (coreDict T.toCore j) Y.d Y.U Y.dict hLc hLd hY.lev.1 hGal a n hDom hDom.2
  have hTC : IsTotallyComplex T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

  have hSc : ∀ f ∈ S, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) := fun f hf => by
    rw [cuspW_wtZ]; exact hS hf

  have hPf : ∀ f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), Y.Pull (f : T.R j) (π f : Rul Y.d.Xo₂ Y.d.c₂) := fun f =>
    (hPull a n _ (cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (by rw [← cuspW_wtZ]; exact f.2)) _).2 (hπP f)

  have p0 : Y.Pull (0 : T.R j) (0 : Rul Y.d.Xo₂ Y.d.c₂) := by
    intro k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero]
  have pAdd : ∀ r₁ r₂ : Rul Y.d.Xo₂ Y.d.c₂, Y.Pull (0 : T.R j) r₁ → Y.Pull (0 : T.R j) r₂ →
      Y.Pull (0 : T.R j) (r₁ + r₂) := by
    intro r₁ r₂ hr₁ hr₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hr₂ k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_add] at e1 e2 ⊢
    rw [e1, e2, add_zero]
  have pSmul : ∀ (c : Y.d.c₂.F) (r : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull (0 : T.R j) r → Y.Pull (0 : T.R j) (c • r) := by
    intro c r hr k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_smul] at e1 ⊢
    rw [e1, mul_zero]
  have pSub : ∀ (f : T.R j) (g₁ g₂ : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull f g₁ → Y.Pull f g₂ → Y.Pull (0 : T.R j) (g₁ - g₂) := by
    intro f g₁ g₂ hg₁ hg₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hg₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hg₂ k hA hk y₂ y' y h1 h2 h3 h4
    have e3 : evR Y.d.Xo₂ Y.d.c₂ (g₁ - g₂) y₂ = evR Y.d.Xo₂ Y.d.c₂ g₁ y₂ - evR Y.d.Xo₂ Y.d.c₂ g₂ y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) g₁ g₂
    rw [e3, e1, e2, sub_self]
    simp only [evR, evalAt_zero]
  have pSmul2 : ∀ (c : Y.d.c₂.F) (h : Rul Y.d.Xo₂ Y.d.c₂) (x : Y.V (wtZ a n)),
      Y.Pull (0 : T.R j) (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) →
        Y.Pull (0 : T.R j) (c • h - ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂)) := by
    intro c h x hp k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hp k hA hk y₂ y' y h1 h2 h3 h4
    have es1 : evR Y.d.Xo₂ Y.d.c₂ (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) y₂ =
        evR Y.d.Xo₂ Y.d.c₂ h y₂ - evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) h (x : Rul Y.d.Xo₂ Y.d.c₂)
    have es2 : evR Y.d.Xo₂ Y.d.c₂ (c • h - ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂)) y₂ =
        evR Y.d.Xo₂ Y.d.c₂ (c • h) y₂ - evR Y.d.Xo₂ Y.d.c₂ ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) _ _
    have es3 : evR Y.d.Xo₂ Y.d.c₂ (c • h) y₂ = algebraMap Y.d.c₂.F k c * evR Y.d.Xo₂ Y.d.c₂ h y₂ := by
      simp only [evR, evalAt_smul]
    have es4 : evR Y.d.Xo₂ Y.d.c₂ ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) y₂ =
        algebraMap Y.d.c₂.F k c * evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      (map_smul ((evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂).comp (Y.V (wtZ a n)).subtype) c x).trans (Algebra.smul_def c _)
    rw [es2, es3, es4, ← mul_sub, ← es1, e1]
    simp only [evR, evalAt_zero, mul_zero]
  set C : Submodule T.Q.c.F (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)) :=
    (Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype with hC
  have hCspan : C = Submodule.span T.Q.c.F ((cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype ⁻¹' S) := by
    rw [hC, ← Submodule.comap_map_eq_of_injective (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).injective_subtype
      (Submodule.span T.Q.c.F ((cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype ⁻¹' S)), Submodule.map_span,
      Set.image_preimage_eq_of_subset]
    intro f hf
    exact ⟨⟨f, hSc f hf⟩, rfl⟩
  have hCQ : ∀ x ∈ C, π x ∈
      (Submodule.span Y.d.c₂.F {g | ∃ f ∈ S, Y.Pull f g}).comap (Y.V (wtZ a n)).subtype := by
    rw [hCspan]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨(y : T.R j), hy, hPf y⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy => rw [π.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  have key : ∀ h ∈ Submodule.span Y.d.c₂.F {g | ∃ f ∈ S, Y.Pull f g},
      ∃ x : Y.V (wtZ a n), x ∈ Submodule.span Y.d.c₂.F (π '' (C : Set (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)))) ∧
        Y.Pull (0 : T.R j) (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨f, hfS, hpf⟩ := hh
      refine ⟨π ⟨f, hSc f hfS⟩, Submodule.subset_span ⟨⟨f, hSc f hfS⟩, Submodule.subset_span hfS, rfl⟩, ?_⟩
      exact pSub f _ _ hpf (hPf _)
    | zero => exact ⟨0, zero_mem _, by simpa using p0⟩
    | add h₁ h₂ _ _ ih₁ ih₂ =>
      obtain ⟨x₁, hx₁, p₁⟩ := ih₁
      obtain ⟨x₂, hx₂, p₂⟩ := ih₂
      refine ⟨x₁ + x₂, add_mem hx₁ hx₂, ?_⟩
      have : h₁ + h₂ - ((x₁ + x₂ : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) =
          (h₁ - (x₁ : Rul Y.d.Xo₂ Y.d.c₂)) + (h₂ - (x₂ : Rul Y.d.Xo₂ Y.d.c₂)) := by
        rw [Submodule.coe_add]; abel
      rw [this]
      exact pAdd _ _ p₁ p₂
    | smul c h _ ih =>
      obtain ⟨x, hx, p⟩ := ih
      exact ⟨c • x, Submodule.smul_mem _ _ hx, pSmul2 c h x p⟩
  have hu := GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover D T j Y e o hT hj hY hY.unit hY.modelW a n hDom 0 (zero_mem _)
  have hDiff : ∀ δ ∈ differentIdeal ℤ (𝓞 Y.d.c₂.F), ∀ g ∈ Y.latOver (wtZ a n) S,
      δ • g ∈ Submodule.span (𝓞 Y.d.c₂.F) (π '' ((GlobalTheory.AllWt.latW (T.U j) (wtZ a n) ⊓ C.restrictScalars (𝓞 T.Q.c.F) :
        Submodule (𝓞 T.Q.c.F) (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))) : Set _)) := by
    intro δ hδ g hg
    have hgl := (Submodule.mem_inf.1 hg).1
    have hgP := (Submodule.mem_inf.1 hg).2
    obtain ⟨x, hx, px⟩ := key _ hgP
    have hgx : ((g : Rul Y.d.Xo₂ Y.d.c₂) - (x : Rul Y.d.Xo₂ Y.d.c₂)) = 0 :=
      hu.unique ⟨sub_mem g.2 x.2, px⟩ ⟨zero_mem _, p0⟩
    have hgx' : g = x := Subtype.ext (sub_eq_zero.1 hgx)
    have h1 := hπD C δ hδ g hgl (hgx' ▸ hx)
    have hset : {f | f ∈ C ∧ f ∈ GlobalTheory.AllWt.latW (T.U j) (wtZ a n)} =
        ((GlobalTheory.AllWt.latW (T.U j) (wtZ a n) ⊓ C.restrictScalars (𝓞 T.Q.c.F) :
          Submodule (𝓞 T.Q.c.F) (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))) : Set _) := by
      ext f
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact And.comm
    rw [hset] at h1
    exact h1
  refine GlobalTheory.SlopeDifferent.slope_sq_sub_le_of_different_smul (K := T.Q.c.F) (K' := Y.d.c₂.F) _ _ π _ _ hG.1 hG₂.1
    ?_ hπli ?_ ?_ ?_ hDiff
  · intro σ f
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  · have hle : Y.latOver (wtZ a n) S ≤ GlobalTheory.AllWt.latW Y.U (wtZ a n) := inf_le_left
    haveI := isNoetherian_of_fg_of_noetherian _ hG₂.2.1
    have h1 := (IsNoetherian.noetherian ((Y.latOver (wtZ a n) S).comap (GlobalTheory.AllWt.latW Y.U (wtZ a n)).subtype)).map
      (GlobalTheory.AllWt.latW Y.U (wtZ a n)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h1
  · intro σ' x
    exact (hπN σ' x).trans (hNc _ _ x)
  · intro x hx
    obtain ⟨hxl, hxC⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨(hπlat x).2 hxl, ?_⟩
    exact hCQ x hxC

end GlobalTheory.CoreRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcFormLocFormChernFormula
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

noncomputable section

namespace GlobalTheory.SecForm.DdcLoc

section Calc

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {z : E}

theorem del_del_comm {u : E → ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    del (fun x => del u x v) z w = del (fun x => del u x w) z v := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e : ∀ a b, del (fun x => del u x a) z b = (1 / 2 : ℂ) •
      (del (fun x => fderiv ℝ u x a) z b - I • del (fun x => fderiv ℝ u x (I • a)) z b) := by
    intro a b
    rw [show (fun x => del u x a) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ u x a - I • fderiv ℝ u x (I • a)) from rfl,
      del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul I)),
      del_sub (h1 _) ((h1 _).fun_const_smul I), del_const_smul _ (h1 _)]
    rfl
  rw [e, e]
  simp only [del_apply, fderiv_fderiv_apply hu, smul_eq_mul]
  rw [hs.eq w, hs.eq w, hs.eq (I • w), hs.eq (I • w)]
  ring

theorem dbar_dbar_comm {u : E → ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    dbar (fun x => dbar u x v) z w = dbar (fun x => dbar u x w) z v := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e : ∀ a b, dbar (fun x => dbar u x a) z b = (1 / 2 : ℂ) •
      (dbar (fun x => fderiv ℝ u x a) z b + I • dbar (fun x => fderiv ℝ u x (I • a)) z b) := by
    intro a b
    rw [show (fun x => dbar u x a) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ u x a + I • fderiv ℝ u x (I • a)) from rfl,
      dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul I), dbar_const_smul _ (h1 _)]
    rfl
  rw [e, e]
  simp only [dbar_apply, fderiv_fderiv_apply hu, smul_eq_mul]
  rw [hs.eq w, hs.eq w, hs.eq (I • w), hs.eq (I • w)]
  ring

theorem contDiffAt_del_at {u : E → ℂ} {j k : WithTop ℕ∞} (hu : ContDiffAt ℝ k u z)
    (hjk : j + 1 ≤ k) (ξ : E) : ContDiffAt ℝ j (fun x => del u x ξ) z :=
  MContDiffAt.mdel (A := fun x => (of fun _ _ => u x : Matrix Unit Unit ℂ)) (fun _ _ => hu) hjk ξ () ()

theorem contDiffAt_dbar_at {u : E → ℂ} {j k : WithTop ℕ∞} (hu : ContDiffAt ℝ k u z)
    (hjk : j + 1 ≤ k) (ξ : E) : ContDiffAt ℝ j (fun x => dbar u x ξ) z :=
  MContDiffAt.mdbar (A := fun x => (of fun _ _ => u x : Matrix Unit Unit ℂ)) (fun _ _ => hu) hjk ξ () ()

end Calc

end GlobalTheory.SecForm.DdcLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLogPlusConstant
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ChainLog

theorem loc_fn_eventuallyEq {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (u : M → ℝ) (x : A.Pt) :
    A.loc (A.fn u) x.1.1 =ᶠ[𝓝 x.crd] fun v => algebraMap ℂ (Alt n) ((u ((A.e x.1.1).symm v) : ℝ) : ℂ) := by
  filter_upwards [(A.e x.1.1).open_target.mem_nhds ((A.e x.1.1).map_source x.2)] with v hv
  rw [HolAtlas.loc, dif_pos hv]
  rfl

theorem delAt_fun {n : ℕ} (g : V n → ℂ) (v : V n) :
    delAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ a, GlobalTheory.del g v (GlobalTheory.GoodMetric.coordVec a) • dz a := by
  simp only [delAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dbarAt_fun {n : ℕ} (g : V n → ℂ) (v : V n) :
    dbarAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ b, GlobalTheory.dbar g v (GlobalTheory.GoodMetric.coordVec b) • dzb b := by
  simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

end GlobalTheory.ChainLog

namespace GlobalTheory.ChainLog

theorem ddc_fn_log_add : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ), A.SmoothOn Set.univ (fun y => (f y : ℂ)) → (∀ y, 0 ≤ f y) →
    ∀ t : ℝ, 0 < t → A.ddc (A.fn (fun y => Real.log (f y + t))) =
      A.fn (fun y => 1 / (f y + t)) * A.ddc (A.fn f) - A.fn (fun y => 1 / (f y + t) ^ 2) * (GlobalTheory.HermFrame.kappa • (A.del (A.fn f) * A.dbar (A.fn f))) := by
  intro M _ n A f hf hf0 t ht
  funext x
  set e := A.e x.1.1 with he
  set v0 := x.crd with hv0
  set w : V n → ℝ := fun v => f (e.symm v) with hwdef
  have hpt : e.symm v0 = x.pt := e.left_inv x.2
  have hw0 : w v0 = f x.pt := by simp only [hwdef, hpt]
  have hnhds : e.target ∈ 𝓝 v0 := e.open_target.mem_nhds (e.map_source x.2)
  have hwS : ContDiffAt ℝ ∞ w v0 := by
    have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf x.1.1)
    have h2 : ContDiffOn ℝ ∞ w e.target :=
      (h1.mono fun v hv => ⟨hv, trivial⟩).congr fun v _ => by simp [hwdef, he]
    exact h2.contDiffAt hnhds
  have hw : ContDiffAt ℝ 2 w v0 := hwS.of_le (WithTop.coe_le_coe.2 le_top)
  have hne : w v0 + t ≠ 0 := by rw [hw0]; linarith [hf0 x.pt]
  have hh : ContDiffAt ℝ 2 (fun s : ℝ => Real.log (s + t)) (w v0) :=
    (contDiffAt_id.add contDiffAt_const).log hne
  have hlw : ContDiffAt ℝ 2 (fun v => Real.log (w v + t)) v0 := hh.comp v0 hw
  have hL : ∀ p q, GlobalTheory.leviForm (fun v => Real.log (w v + t)) v0 p q =
      ((deriv (fun s : ℝ => Real.log (s + t)) (w v0) : ℝ) : ℂ) * GlobalTheory.leviForm w v0 p q
        + ((deriv (deriv (fun s : ℝ => Real.log (s + t))) (w v0) : ℝ) : ℂ) *
          (GlobalTheory.del (fun v => (w v : ℂ)) v0 p * GlobalTheory.dbar (fun v => (w v : ℂ)) v0 q) :=
    fun p q => GlobalTheory.leviForm_real_comp hh hw p q
  rw [GlobalTheory.deriv_deriv_log_add_const, GlobalTheory.deriv_log_add_const] at hL
  have hddc : ∀ u : M → ℝ, A.ddc (A.fn u) x = GlobalTheory.HermFrame.kappa • delAt (dbarAt fun v => algebraMap ℂ (Alt n) ((u (e.symm v) : ℝ) : ℂ)) v0 :=
    fun u => GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq A _ x _ (loc_fn_eventuallyEq A u x)
  have hdel : A.del (A.fn f) x = ∑ a, GlobalTheory.del (fun v => (w v : ℂ)) v0 (GlobalTheory.GoodMetric.coordVec a) • dz a := by
    change delAt (A.loc (A.fn f) x.1.1) x.crd = _
    rw [GlobalTheory.SecForm.DdcGerm.delAt_germ (loc_fn_eventuallyEq A f x), delAt_fun]
  have hdbar : A.dbar (A.fn f) x = ∑ b, GlobalTheory.dbar (fun v => (w v : ℂ)) v0 (GlobalTheory.GoodMetric.coordVec b) • dzb b := by
    change dbarAt (A.loc (A.fn f) x.1.1) x.crd = _
    rw [GlobalTheory.SecForm.DdcGerm.dbarAt_germ (loc_fn_eventuallyEq A f x), dbarAt_fun]
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply]
  rw [hddc, hddc, hdel, hdbar]
  rw [show (fun v => algebraMap ℂ (Alt n) (((fun y => Real.log (f y + t)) (e.symm v) : ℝ) : ℂ))
      = fun v => algebraMap ℂ (Alt n) ((Real.log (w v + t) : ℝ) : ℂ) from rfl,
    delAt_dbarAt_fun hlw, show (fun v => algebraMap ℂ (Alt n) ((f (e.symm v) : ℝ) : ℂ))
      = fun v => algebraMap ℂ (Alt n) ((w v : ℝ) : ℂ) from rfl, delAt_dbarAt_fun hw]
  simp only [HolAtlas.fn, ← hpt, ← Algebra.smul_def, ofValues, GlobalTheory.HermFrame.ddc, hL, AddSubmonoidClass.coe_finset_sum,
    Subalgebra.coe_smul, sym, Finset.sum_mul_sum, smul_mul_smul_comm, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib,
    ← sub_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp only [hwdef]
  push_cast
  ring

end GlobalTheory.ChainLog
end
end

