import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0076

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProdExpOppositeTranslates
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ProdTransl

theorem comp_inv_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G)
    (k : ℕ) : ρ ≫ (x ^ k)⁻¹ = ((ρ ≫ x) ^ k)⁻¹ :=
  (map_inv (preHom (G := G) ρ) (x ^ k)).trans (congrArg (·⁻¹) (map_pow (preHom (G := G) ρ) x k))

theorem value_identity {A A' B O : Type} [CommGroup A] [CommGroup A'] [CommGroup B] [CommRing O] (Θ : B → B → B → Oˣ)
    (θ' : A' → A' → A' → Oˣ) (p : A →* B) (q : A →* A') (W : A → Oˣ) (hc : IsCub θ')
    (h : ∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 =
      W (x * y * u) * W x * W y * W u * Θ (p x) (p y) (p u)) (k : ℕ) (x y : A) (hx : q x = 1) (X Y : B) (hX : X = p x)
    (hY : Y = p y) (n n' : Oˣ) (hn : n * W 1 = W x) (hn' : n' * W 1 = W (x ^ k)⁻¹) (s s' t : O)
    (ht : t = (cubN Θ k 1 X Y * Θ Y (X ^ k) (X ^ k)⁻¹ * (n ^ k * n')).val * (s * s')) :
    (W y).val ^ (k + 1) * t = (W (x * y)).val ^ k * s * ((W ((x ^ k)⁻¹ * y)).val ^ 1 * s') := by
  have e := cubN_descent_opposite A A' Oˣ (fun a b c => Θ (p a) (p b) (p c)) θ' q W hc h k x y hx
  have c : cubN (fun a b c => Θ (p a) (p b) (p c)) k 1 x y = cubN Θ k 1 (p x) (p y) := by
    simp only [cubN, map_mul, map_one, map_pow]
  rw [c, map_inv, map_pow, ← hX, ← hY, ← hn, ← hn', mul_comm y, mul_pow] at e
  have e' : W y ^ (k + 1) * (cubN Θ k 1 X Y * Θ Y (X ^ k) (X ^ k)⁻¹ * (n ^ k * n')) =
      W (x * y) ^ k * W ((x ^ k)⁻¹ * y) := by
    apply mul_right_cancel (b := W 1 ^ (k + 1))
    rw [← e, pow_succ (W 1)]
    generalize W y ^ (k + 1) = u₁
    generalize W 1 ^ k = u₂
    generalize n ^ k = u₃
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel
  have e'' := congrArg Units.val e'
  rw [Units.val_mul, Units.val_mul (W (x * y) ^ k), Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at e''
  rw [ht, ← _root_.mul_assoc, e'']
  ring

theorem exists_prod {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    {T : Over S} (x : T ⟶ G) (k : ℕ)
    (σ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => (k : ℤ))))
    (ϑ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => ((1 : ℕ) : ℤ))))
    (ν : LB.Gen (LB.LinComb L.L (K := Fin 2) ![x.left, (1 : T ⟶ G).left] ![-1, 1])) (hν : ν.IsGen)
    (ν' : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(x ^ k)⁻¹.left, (1 : T ⟶ G).left] ![-1, 1])) (hν' : ν'.IsGen) :
    ∃ τ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => ((k + 1 : ℕ) : ℤ))),
      ∀ (T' : Over S) (ρ : T' ⟶ T ⊗ G) (z : T'.left) (J), Good L.L z J →
        sval τ ρ.left z J =
          (cubN (cubV c z J) k 1 (ρ ≫ fst T G ≫ x) (ρ ≫ snd T G) *
            cubV c z J (ρ ≫ snd T G) ((ρ ≫ fst T G ≫ x) ^ k) ((ρ ≫ fst T G ≫ x) ^ k)⁻¹ *
            (val ν (ρ.left ≫ (fst T G).left) z J ^ k * val ν' (ρ.left ≫ (fst T G).left) z J)).val *
          (sval σ (ρ.left ≫ (translT G x).left) z J * sval ϑ (ρ.left ≫ (translT G (x ^ k)⁻¹).left) z J) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN c (1 : T ⊗ G ⟶ G) (fst T G ≫ x) (snd T G) k
  have hX : ∀ {T' : Over S} (ρ : T' ⟶ T), ρ ≫ (x ^ k)⁻¹ = ((ρ ≫ x) ^ k)⁻¹ := fun ρ => comp_inv_pow ρ x k
  have e₁ : ∀ u : T ⟶ G, (translT G u).left ≫ (snd T G).left = ((fst T G ≫ u) * snd T G).left := fun u =>
    congrArg (fun q => q.left) (lift_snd (fst T G) (translPt G u))
  have e₂ : (fst T G).left ≫ (1 : T ⟶ G).left = (1 : T ⊗ G ⟶ G).left :=
    congrArg (fun q => q.left) (MonObj.comp_one (M := G) (fst T G) : fst T G ≫ (1 : T ⟶ G) = 1)
  have e₃ : (fst T G).left ≫ (x ^ k)⁻¹.left = ((fst T G ≫ x) ^ k)⁻¹.left := congrArg (fun q => q.left) (hX (fst T G))
  have e₄ : (fst T G).left ≫ x.left = (fst T G ≫ x).left := rfl
  have hu : (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ t (LB.pullGen L.L (thφ G (x3 G)) thε c.t
      (lift (snd T G) (lift ((fst T G ≫ x) ^ k) ((fst T G ≫ x) ^ k)⁻¹)).left))
      (LB.mulGen L.L _ _ _ _ (GeneratorPullback.powGen L.L _ _ (LB.pullGen L.L _ _ ν (fst T G).left) k)
        (LB.pullGen L.L _ _ ν' (fst T G).left))).IsGen :=
    DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ c.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hν _) k)
        (DVR.pullGen_isGen _ _ _ _ hν' _))
  obtain ⟨τ, hτ⟩ := exists_sec L.isLB (φ' := fun _ : Fin 1 => (snd T G).left) (ε' := fun _ => ((k + 1 : ℕ) : ℤ))
    (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
        ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
          ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl
            (prod_cub (snd T G) ((fst T G ≫ x) ^ k) ((fst T G ≫ x) ^ k)⁻¹ h)))
          (Fintype.prod_sum_type _))) (Fintype.prod_sum_type _))).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, e₁, e₂, e₃, e₄, hX, _root_.one_mul, mul_inv_cancel, mul_inv_cancel_right]
      rw [mul_comm (snd T G) ((fst T G ≫ x) ^ k), mul_comm (snd T G) ((fst T G ≫ x) ^ k)⁻¹]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (genSec _ hu) (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec σ (translT G x).left)
      (H1.SectionArithmetic.pullSec ϑ (translT G (x ^ k)⁻¹).left)))
  refine ⟨τ, fun T' ρ z J hJ => (hτ _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val ?_))
    ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)
      (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)))))⟩
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((hv T' ρ z J hJ).trans ?_) ((val_cub c ρ hJ _ _ _).trans ?_)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((map_pow _ _ _).trans (congrArg (· ^ k) (val_pull hJ _ _ _)))
      (val_pull hJ _ _ _))))
  · rw [MonObj.comp_one]
  · have a : ρ ≫ (fst T G ≫ x) ^ k = (ρ ≫ fst T G ≫ x) ^ k := map_pow (preHom (G := G) ρ) _ _
    have b : ρ ≫ ((fst T G ≫ x) ^ k)⁻¹ = (ρ ≫ (fst T G ≫ x) ^ k)⁻¹ := map_inv (preHom (G := G) ρ) _
    rw [b, a]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

noncomputable def push (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun u => (Over.map (thick R I e)).map u ≫ fstG I e G) fun a b =>
    Over.OverMorphism.ext ((isGrpPullback_pullback G (thick R I e)).2 T a b _ _ rfl rfl).symm

theorem prodExp_of_normAt (hG : GlobalFnsSt) (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]
    (a a' : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) (k : ℕ) (hx : U.TorPt a x) (hx' : U.TorPt a' (x ^ k)⁻¹)
    (ν) (hν : U.NormAt x ν) (ν') (hν' : U.NormAt (x ^ k)⁻¹ ν')
    (σ : U.SecGT (TA R W) k) (ϑ : U.SecGT (TA R W) 1) (f) (g) (hf : U.ExpT (TA R W) k σ f)
    (hg : U.ExpT (TA R W) 1 ϑ g) :
    ∃ τ : U.SecGT (TA R W) (k + 1), U.ProdExp (TA R W) (twist a f) (twist a' g) τ := by
  obtain ⟨τ, hτ⟩ := exists_prod U.P.c x k σ ϑ ν hν.1 ν' hν'.1
  refine ⟨τ, fun e => ?_⟩
  obtain ⟨s, hs⟩ := expansion_translate_torus hG R I D A G U W a x hx k σ f hf e
  obtain ⟨s', hs'⟩ := expansion_translate_torus hG R I D A G U W a' _ hx' 1 ϑ g hg e
  refine ⟨s, s', fun Z y rG rB h₁ h₂ h₃ z JG J hJG hJ => ?_⟩
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let yo : T ⟶ thickObj R I e G := Over.homMk y rfl
  have hb : rG ≫ (TA R W ⊗ G).hom = T.hom ≫ thick R I e := by
    rw [← Over.w (snd (TA R W) G), ← Category.assoc, h₁, Category.assoc, Over.w (fstG I e G)]
    exact (Category.assoc _ _ _).symm
  let ρ : (Over.map (thick R I e)).obj T ⟶ TA R W ⊗ G := Over.homMk rG hb
  let x₀ : (Over.map (thick R I e)).obj T ⟶ G := ρ ≫ fst _ _ ≫ x
  let xe : T ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift x₀.left T.hom (Over.w x₀)) (pullback.lift_snd _ _ _)
  have hxl : xe.left ≫ pullback.fst G.hom (thick R I e) = x₀.left := pullback.lift_fst _ _ _
  have hxe : ρ ≫ fst _ _ ≫ x = push I e G T xe := Over.OverMorphism.ext hxl.symm
  have hy : ρ ≫ snd _ _ = push I e G T yo := Over.OverMorphism.ext h₁
  have hxe' : ρ ≫ fst _ _ ≫ (x ^ k)⁻¹ = push I e G T (xe ^ k)⁻¹ := by
    rw [map_inv, map_pow, ← hxe, ← Category.assoc, ← Category.assoc]
    exact comp_inv_pow _ x k
  have tr : ∀ (u : TA R W ⟶ G) (ue : T ⟶ thickObj R I e G), ρ ≫ fst _ _ ≫ u = push I e G T ue →
      (ue * yo).left ≫ (fstG I e G).left = rG ≫ (translPt G u).left := fun u ue hu =>
    congrArg (fun q => q.left) ((map_mul (push I e G T) ue yo).trans
      ((congrArg₂ (· * ·) hu.symm hy.symm).trans (MonObj.comp_mul ρ (fst _ _ ≫ u) (snd _ _)).symm))
  have pt : ∀ (u : TA R W ⟶ G) (ue : T ⟶ thickObj R I e G), ρ ≫ fst _ _ ≫ u = push I e G T ue →
      ue.left ≫ (fstG I e G).left = (rG ≫ (fst (TA R W) G).left) ≫ u.left := fun u ue hu =>
    (congrArg (fun q => q.left) hu.symm).trans (Category.assoc _ _ _).symm
  have h1 : ρ ≫ fst _ _ ≫ (1 : TA R W ⟶ G) = push I e G T 1 := by
    rw [map_one, MonObj.comp_one, MonObj.comp_one]
  have hq : GlobalTheory.TorusCoord.im (U.gt e) xe = 1 := by
    have : (ρ ≫ fst _ _) ≫ (1 : TA R W ⟶ D.P.A) = 1 := MonObj.comp_one _
    exact (Over.OverMorphism.ext (hx e Z (rG ≫ (fst (TA R W) G).left) xe.left (pt x xe hxe)).1).trans this
  obtain ⟨a₁, a₂⟩ := hs Z y (xe * yo).left rG rB h₁ h₂ h₃ (tr x xe hxe) z JG J hJG hJ
  obtain ⟨b₁, b₂⟩ := hs' Z y ((xe ^ k)⁻¹ * yo).left rG rB h₁ h₂ h₃ (tr _ _ hxe') z JG J hJG hJ
  refine ⟨a₁, b₁, Eq.trans ?_ (congrArg₂ (· * ·) a₂ b₂)⟩
  exact value_identity (O := Z.presheaf.stalk z) (cubV U.P.c (T := (Over.map (thick R I e)).obj T) z JG)
    (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J) (push I e G T)
    (MonoidHom.mk' (fun u : T ⟶ thickObj R I e G => GlobalTheory.TorusCoord.im (U.gt e) u) (GlobalTheory.TorusCoord.im_mul (U.gt e)))
    (fun u => U.wv e u.left z JG J) (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ)
    (U.w_vals e T z JG J hJG hJ (fun u => U.wv e u.left z JG J) (fun _ => rfl)).2.2 k xe yo hq _ _ hxe hy _ _
    (hν.2 e Z (rG ≫ (fst (TA R W) G).left) xe.left (1 : T ⟶ thickObj R I e G).left (pt x xe hxe) (pt 1 1 h1)
      z JG J hJG hJ)
    (hν'.2 e Z (rG ≫ (fst (TA R W) G).left) (xe ^ k)⁻¹.left (1 : T ⟶ thickObj R I e G).left (pt _ _ hxe') (pt 1 1 h1)
      z JG J hJG hJ) _ _ _ (hτ _ ρ z JG hJG)

end GlobalTheory.UU.ProdTransl

theorem GlobalTheory.UU.prodExp_opposite_translates : GlobalFnsSt → AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (a : Multiplicative D.X →* Wˣ) (x : TA V W ⟶ G), U.TorPt a x → ∀ (k : ℕ) (σ : U.SecGT (TA V W) k) (ϑ : U.SecGT (TA V W) 1) (f) (g), U.ExpT (TA V W) k σ f → U.ExpT (TA V W) 1 ϑ g → ∃ σ'' : U.SecGT (TA V W) (k + 1), U.ProdExp (TA V W) (twist a f) (twist (a ^ k)⁻¹ g) σ'' := by
  intro hG V _ _ _ hV D A G _ _ U W _ _ _ hW a x hx k σ ϑ f g hf hg
  have hm := (GlobalTheory.UU.torPt_group hG V _ D A G U W).2
  have hx' : U.TorPt (a ^ k)⁻¹ (x ^ k)⁻¹ := (hm _ a _ x ((hm a a x x hx).2.2 k)).2.1
  obtain ⟨ν, hν⟩ := GlobalTheory.NormGen.exists_normAt V hV D A G U W hW a x hx
  obtain ⟨ν', hν'⟩ := GlobalTheory.NormGen.exists_normAt V hV D A G U W hW _ _ hx'
  exact ProdTransl.prodExp_of_normAt hG U a _ x k hx hx' ν hν ν' hν' σ ϑ f g hf hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointBalancedPowerLift
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalElem

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.TauBalBox

theorem exists_unbox {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (b : LB.Gen (LB.LinComb M (K := K × Fin j) (fun p => φ' p.1 ≫ pr p.2) (fun p => ε p.1))) (hb : b.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb M' φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (y : Z) (J J'),
      Good M y J → Good M' y J' →
      (∏ a, om w y J J' (q ≫ φ' a) ^ ε a) * val t' q y J' = val b q y J := by
  have le : ∀ jN : K → Fin j → M.ι, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ≤
      LB.wchart M (K := K × Fin j) (fun p => φ' p.1 ≫ pr p.2) (fun p => jN p.1 p.2) := fun jN y hy =>
    Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  let b' : LB.Gen (LB.LinComb (LB.LinComb M pr (fun _ => 1)) φ' ε) :=
    ⟨fun jN => res (le jN) (b.s (fun p => jN p.1 p.2))⟩
  have hb' : b'.IsGen := fun jN jN' => unit_ext fun y hy => by
    have e := gen_trans hb (𝟙 Y) y (le jN hy.1) (le jN' hy.2)
    refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le jN) hy.1 _)).trans (e.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb _ φ' ε (𝟙 Y) y jN jN' hy.1 hy.2).trans ?_)
      ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le jN') hy.2 _)))
    rw [trF, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    refine (congrArg (· ^ ε a) (gm_linComb M pr (fun _ => 1) (𝟙 Y ≫ φ' a) y (jN a) (jN' a)
      (Set.mem_iInter.1 hy.1 a) (Set.mem_iInter.1 hy.2 a))).trans ?_
    simp only [zpow_one, Category.assoc, Finset.prod_zpow]
  obtain ⟨t, ht, H⟩ := Transport.exists_transport (linComb_isLB M' hM' φ' ε)
    (linComb_isLB _ (linComb_isLB M hM pr (fun _ => 1)) φ' ε) (LB.linCombIso w φ' ε) (linCombIso_isGen w hw φ' ε) b' hb'
  refine ⟨t, ht, fun Z q y J J' hJ hJ' => ?_⟩
  have hm : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((q ≫ φ' a) ≫ pr i), hJ'.mem _ q⟩
  have E := congrArg (gm q y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
    LB.wchart M' φ' (fun a => J' (q ≫ φ' a)))) (H (fun a i => J ((q ≫ φ' a) ≫ pr i), fun a => J' (q ≫ φ' a)))
  rw [val_of b q y J (fun p => J ((q ≫ φ' p.1) ≫ pr p.2)) (fun p => by rw [Category.assoc])]
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linCombIso w φ' ε q y _ _ hm)
    (gm_res q y inf_le_right hm _))).symm.trans
    (E.symm.trans ((gm_res q y inf_le_left hm _).trans (gm_res q y (le _) hm.1 _)))

theorem prod_two_single {U N : Type} [CommGroup U] [Fintype N] (P Q : N → U) (i l : N) (c : U)
    (hP : ∀ s, s ≠ i → P s = c⁻¹) (hQ : ∀ s, s ≠ l → Q s = c) : ∏ s, P s * Q s = P i * Q l := by
  have h₁ : ∏ s, P s * c = P i * c := Finset.prod_eq_single i (fun s _ hs => by rw [hP s hs, inv_mul_cancel])
    (fun h => absurd (Finset.mem_univ _) h)
  have h₂ : ∏ s, Q s * c⁻¹ = Q l * c⁻¹ := Finset.prod_eq_single l (fun s _ hs => by rw [hQ s hs, mul_inv_cancel])
    (fun h => absurd (Finset.mem_univ _) h)
  have e : ∀ p q : U, p * q = p * c * (q * c⁻¹) := fun p q => by
    rw [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one]
  rw [e (P i), ← h₁, ← h₂, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s _ => e _ _

theorem formEq_elem {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    {j : ℕ} (p : IsPowGrp A' A j) (f g : A ⟶ A) (f' g' : A' ⟶ A') (i l : Fin j)
    (hf : ∀ s, f' ≫ p.pr s = if s = i then p.pr l ≫ f else 1)
    (hg : ∀ s, g' ≫ p.pr s = if s = l then p.pr i ≫ g else 1) :
    FormEq (fun k => (lift (fst A' A' ≫ p.pr l) (snd A' A' ≫ p.pr i)).left ≫ rosatiφ A f g k) rosatiε
      (fun q : Fin 6 × Fin j => rosatiφ A' f' g' q.1 ≫ (p.pr q.2).left) (fun q => rosatiε q.1) := by
  intro U _ h
  let H : (A' ⊗ A' ⟶ A) → U := fun q => h q.left
  let P : Fin j → U := fun s => H ((fst A' A' ≫ f' ≫ p.pr s) * (snd A' A' ≫ p.pr s)) *
    (H (fst A' A' ≫ f' ≫ p.pr s))⁻¹ * (H (snd A' A' ≫ p.pr s))⁻¹
  let Q : Fin j → U := fun s => (H ((fst A' A' ≫ p.pr s) * (snd A' A' ≫ g' ≫ p.pr s)))⁻¹ *
    H (fst A' A' ≫ p.pr s) * H (snd A' A' ≫ g' ≫ p.pr s)
  have e : ∀ s, ∏ a, h (rosatiφ A' f' g' a ≫ (p.pr s).left) ^ rosatiε a = P s * Q s := fun s => by
    haveI := p.hom s
    have := prod_ros f' g' (fst A' A') (snd A' A') (fun q => h (q ≫ (p.pr s).left))
    rw [lift_fst_snd] at this
    simp only [Over.id_left, Category.id_comp, ← Over.comp_left, MonObj.mul_comp, Category.assoc] at this
    refine this.trans ?_
    simp only [P, Q, H, _root_.mul_assoc]
  rw [Fintype.prod_prod_type_right, Finset.prod_congr rfl fun s _ => e s,
    prod_two_single P Q i l (H 1) (fun s hs => by
      simp only [P, hf s, if_neg hs, MonObj.comp_one, _root_.one_mul]
      rw [mul_right_comm, mul_inv_cancel, _root_.one_mul]) (fun s hs => by
      simp only [Q, hg s, if_neg hs, MonObj.comp_one, _root_.mul_one]
      rw [inv_mul_cancel, _root_.one_mul])]
  refine (prod_ros f g _ _ h).trans ?_
  simp only [P, Q, H, hf i, hg l, if_true, Category.assoc, _root_.mul_assoc]

theorem tau_zero_left {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {y : (TK R).left} {J}
    (hJ : Good D.P.L y J) (b : D.X) : val (D.tau 0 b) (𝟙 _) y J = 1 := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 b
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact mul_eq_left.1 t.symm

theorem tauBal_elem : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.TauBimult → ∀ (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g] (a b : D.X → D.X), (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (b y) = D.c y ≫ g) → RosatiAdj D.P.A D.P.L f g → D.TauBal f g a b → ∀ (f' g' : D'.P.A ⟶ D'.P.A) (i l : Fin j), (∀ s, f' ≫ pD.pw.pr s = if s = i then pD.pw.pr l ≫ f else 1) → (∀ s, g' ≫ pD.pw.pr s = if s = l then pD.pw.pr i ≫ g else 1) → D'.TauBal f' g' (fun y => pD.xe.symm (Pi.single i (a (pD.xe y l)))) (fun y => pD.xe.symm (Pi.single l (b (pD.xe y i)))) := by
  intro hG R _ _ j D D' pD hB f g _ _ a b ca cb hr hT f' g' i l hf hg u' hu' hn' x x'
  obtain ⟨u, hu, hn⟩ := exists_ros hG D.P.isAb D.P.isLB f g hr
  have lin : ∀ (f : D.P.A ⟶ D.P.A) (f' : D'.P.A ⟶ D'.P.A) (a : D.X → D.X) (i l : Fin j),
      (∀ s, f' ≫ pD.pw.pr s = if s = i then pD.pw.pr l ≫ f else 1) → (∀ y, D.c (a y) = D.c y ≫ f) → ∀ x,
      cP D' (TK R) (pD.xe.symm (Pi.single i (a (pD.xe x l)))) = cP D' (TK R) x ≫ f' := by
    intro f f' a i l hf ca x
    apply pD.pw.lim.hom_ext
    rintro ⟨s⟩
    show cP D' (TK R) _ ≫ pD.pw.pr s = (cP D' (TK R) x ≫ f') ≫ pD.pw.pr s
    rw [cPoint_pr, AddEquiv.apply_symm_apply, Category.assoc, hf]
    by_cases hs : s = i
    · subst hs
      rw [if_pos rfl, Pi.single_eq_same, ← Category.assoc, cPoint_pr, cP, cP, ca, Category.assoc]
    · rw [if_neg hs, Pi.single_eq_of_ne hs, cPoint_zero, MonObj.comp_one]
  have one : ∀ (f : D.P.A ⟶ D.P.A) [IsMonHom f] (f' : D'.P.A ⟶ D'.P.A) (i l : Fin j),
      (∀ s, f' ≫ pD.pw.pr s = if s = i then pD.pw.pr l ≫ f else 1) → η[D'.P.A] ≫ f' = η[D'.P.A] := by
    intro f _ f' i l hf
    apply pD.pw.lim.hom_ext
    rintro ⟨s⟩
    show (η[D'.P.A] ≫ f') ≫ pD.pw.pr s = η[D'.P.A] ≫ pD.pw.pr s
    haveI := pD.pw.hom s
    haveI := pD.pw.hom l
    rw [Category.assoc, hf, IsMonHom.one_hom (pD.pw.pr s)]
    split_ifs
    · rw [IsMonHom.one_hom]
    · simp [Hom.one_def]
  let ρ : (D'.P.A ⊗ D'.P.A).left ⟶ (D.P.A ⊗ D.P.A).left :=
    (lift (fst D'.P.A D'.P.A ≫ pD.pw.pr l) (snd D'.P.A D'.P.A ≫ pD.pw.pr i)).left
  have hρ : ∀ {T : Over (Spec (CommRingCat.of R))} (p q : T ⟶ D'.P.A), (lift p q).left ≫ ρ =
      (lift (p ≫ pD.pw.pr l) (q ≫ pD.pw.pr i)).left := fun p q => by
    show (lift p q ≫ lift _ _).left = _
    rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_gen D.P.isLB (formEq_elem pD.pw f g f' g' i l hf hg) (LB.pullGen D.P.L _ _ u ρ)
    (pullGen_isGen _ _ _ _ hu _)
  obtain ⟨t, ht, hv⟩ := exists_unbox (pr := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen
    (rosatiφ D'.P.A f' g') rosatiε t₀ ht₀
  have hv' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (D'.P.A ⊗ D'.P.A).left) (y : Z) (J J'), Good D.P.L y J → Good D'.P.L y J' →
      (∏ k, om pD.w y J J' (q ≫ rosatiφ D'.P.A f' g' k) ^ rosatiε k) * val t q y J' = val u (q ≫ ρ) y J :=
    fun Z q y J J' hJ hJ' => (hv Z q y J J' hJ hJ').trans ((hv₀ Z q y J hJ).trans (val_pull hJ _ _ _))
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : zero2 D'.P.A ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D'.P.A] η[D'.P.A])
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have uq := gen_unique D'.P.isLB _ (zero2 D'.P.A) he sj hu' ht (fun s I' hI' => by
      obtain ⟨I, hI⟩ := exists_good_at D.P.isLB s
      have o : (η[D'.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = 1 := by simp [Hom.one_def]
      have p := prod_ros f' g' η[D'.P.A] η[D'.P.A] (om pD.w s I I')
      rw [one f f' i l hf, one g g' l i hg, show η[D'.P.A] * η[D'.P.A] = η[D'.P.A] by rw [o, _root_.mul_one]] at p
      have v' := val_corr hI' hn' (𝟙 _)
      rw [val_pull hI', Category.id_comp, val_one] at v'
      have v := val_corr hI hn (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at v
      have k := (congrArg₂ (· * ·) p rfl).symm.trans (hv' _ (zero2 D'.P.A) s I I' hI hI')
      haveI := pD.pw.hom i
      haveI := pD.pw.hom l
      rw [show zero2 D'.P.A ≫ ρ = _ from hρ _ _, IsMonHom.one_hom, IsMonHom.one_hom] at k
      have k' := k.trans v
      refine v'.trans (Eq.symm ?_)
      simpa using k') _ (D'.pt2 x x') y J' hJ'
  have p := prod_ros f' g' (cP D' (TK R) x) (cP D' (TK R) x') (om pD.w y J J')
  have key' := (congrArg₂ (· * ·) p uq.symm).symm.trans (hv' _ (D'.pt2 x x') y J J' hJ hJ')
  have t₁ := tau_box pD hJ hJ' (pD.xe.symm (Pi.single i (a (pD.xe x l)))) x'
  have t₂ := tau_box pD hJ hJ' x (pD.xe.symm (Pi.single l (b (pD.xe x' i))))
  rw [lin f f' a i l hf ca, AddEquiv.apply_symm_apply, Finset.prod_eq_single i (fun s _ hs => by
    rw [Pi.single_eq_of_ne hs, tau_zero_left hB hJ]) (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same] at t₁
  rw [lin g g' b l i hg cb, AddEquiv.apply_symm_apply, Finset.prod_eq_single l (fun s _ hs => by
    rw [Pi.single_eq_of_ne hs, tauK_symm hJ, tau_zero_left hB hJ]) (fun h => absurd (Finset.mem_univ _) h),
    Pi.single_eq_same] at t₂
  have E := val_corr hJ (hT u hu hn (pD.xe x l) (pD.xe x' i)) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, Category.id_comp] at E
  have z : D'.pt2 x x' ≫ ρ = D.pt2 (pD.xe x l) (pD.xe x' i) := by
    refine (hρ _ _).trans ?_
    rw [Category.assoc, Category.assoc, pD.c_pr, pD.c_pr]; rfl
  rw [← z, ← t₁, ← t₂, ← key'] at E
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have E' := congrArg Additive.ofMul E
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at E' ⊢
  rw [← sub_eq_zero] at E' ⊢
  refine Eq.trans ?_ E'
  abel

end GlobalTheory.TauBalElem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothOfRelativeDimensionOfGeneric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericDim

theorem smoothOfRelativeDimension_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (g : ℕ), SmoothOfRelativeDimension g (pullback.snd G.hom (jK R)) → SmoothOfRelativeDimension g G.hom := by
  intro R _ _ G _ _ _ g hg
  have hdense := (ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK (V := R)).denseRange
  have hloc : ∀ x : G.left, ∃ W : G.left.Opens, x ∈ W ∧
      SmoothOfRelativeDimension g (W.ι ≫ G.hom) := by
    intro x
    obtain ⟨n, W, hxW, hW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom x
    refine ⟨W, hxW, ?_⟩
    have hopen : IsOpen (G.hom '' (W : Set G.left)) := G.hom.isOpenMap _ W.isOpen
    obtain ⟨y, w, hwW, hwy⟩ := hdense.exists_mem_open hopen ⟨G.hom x, x, hxW, rfl⟩
    obtain ⟨z, hz, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := jK R) w y hwy
    have hzW : pullback.fst G.hom (jK R) z ∈ W := by rw [hz]; exact hwW
    have hng : n = g :=
      ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback G.hom (jK R)) hW hg z hzW
    exact hng ▸ hW
  have i1 : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension g)
  choose W hxW hW using hloc
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩) hW

end GlobalTheory.GenericDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionFieldStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by
  first | exact @GlobalTheory.psiRel_of_pullB | exact GlobalTheory.psiRel_of_pullB | (intros; apply GlobalTheory.psiRel_of_pullB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueExpansionOfChartExpansionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.valueExpansion_of_chartExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by
  first | exact @GlobalTheory.UU.expF_of_expands | exact GlobalTheory.UU.expF_of_expands | (intros; apply GlobalTheory.UU.expF_of_expands <;> assumption)
end

