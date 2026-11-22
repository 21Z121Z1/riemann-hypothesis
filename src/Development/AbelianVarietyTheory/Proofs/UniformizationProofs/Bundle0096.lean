import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueBiTriv
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.EvenCub

section Alg
variable {A A' B U : Type} [CommGroup A] [CommGroup A'] [CommGroup B] [CommGroup U]

def diff₃ (k : A → U) (x y u : A) : U :=
  k (x * y * u) * (k (x * y))⁻¹ * (k (x * u))⁻¹ * (k (y * u))⁻¹ * k x * k y * k u * (k 1)⁻¹

def diffQ (k : A → U) (x a : A) : U := k (x * a) * (k x)⁻¹ * (k x)⁻¹ * (k a)⁻¹ * k 1 * k 1

def diffS (k : A → U) (x : A) : U := k x⁻¹ * (k x)⁻¹

def cubeDefect (θ : A → A → A → U) (υ : A → U) (x y u a b d : A) : U :=
  θ (x * y) u (a * b * d) * θ (x * y) (a * b) d * θ u (a * b) d * θ x y d * θ u a b * υ (x * y) * υ (x * u) *
    υ (y * u) * (θ x u (a * d) * θ x a d * θ u a d * θ y u (b * d) * θ y b d * θ u b d * θ x y u * υ (x * y * u) *
      υ x * υ y * υ u)⁻¹

def evenDefect (σ υ : A → U) (x a : A) : U := υ x⁻¹ * σ x * σ x * σ a * (σ (x * a) * υ x)⁻¹

end Alg

section Rep
variable {S X : Scheme.{0}} {L : LB X} {Y : Over S}

def Rep (L : LB X) (Y : Over S) (F : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U)
    (v : ∀ (T : Over S), (T ⟶ Y) → ∀ z : T.left, ((T.left ⟶ X) → L.ι) → (T.left.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ (T : Over S) (σ : T ⟶ Y) (z : T.left) (J), Good L z J → val t σ.left z J = v T σ z J

variable {F F' : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U}
  {v v' : ∀ (T : Over S), (T ⟶ Y) → ∀ z : T.left, ((T.left ⟶ X) → L.ι) → (T.left.presheaf.stalk z)ˣ}

theorem Rep.mul (h : Rep L Y F v) (h' : Rep L Y F' v') :
    Rep L Y (fun U _ k => F U k * F' U k) (fun T σ z J => v T σ z J * v' T σ z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ k => DVR.prod_sum₂ _ (hF U k) (hF' U k), fun T σ z J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T σ z J hJ) (hv' T σ z J hJ))⟩

theorem Rep.inv (h : Rep L Y F v) : Rep L Y (fun U _ k => (F U k)⁻¹) (fun T σ z J => (v T σ z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ k => ?_, fun T σ z J hJ =>
    (val_inv _ _).trans (congrArg (·⁻¹) (hv T σ z J hJ))⟩
  show _ = (F U k)⁻¹
  rw [← hF U k, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun a _ => zpow_neg _ _

theorem Rep.pull {K : Type} [Fintype K] {Y' : Over S} {φ : K → (Y'.left ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ Y')
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (p.left ≫ φ k) ^ ε k = F U h) :
    Rep L Y F (fun _ σ z J => val t (σ ≫ p).left z J) :=
  ⟨K, inferInstance, _, _, LB.pullGen L φ ε t p.left, DVR.pullGen_isGen _ _ _ _ ht _, hF,
    fun _ _ _ _ hJ => val_pull hJ _ _ _⟩

theorem Rep.exists_gen (hL : L.IsLB) (h : Rep L Y F v) {K : Type} [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), F U h = ∏ k, h (φ k) ^ ε k) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (T : Over S) (σ : T ⟶ Y) (z : T.left) (J), Good L z J → val t σ.left z J = v T σ z J := by
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := h
  obtain ⟨t, ht, hv⟩ := Geo.Tor.exists_gen hL (φ' := φ) (ε' := ε) (fun U _ k => (hF' U k).trans (hF U k)) t' ht'
  exact ⟨t, ht, fun T σ z J hJ => (hv _ _ z J hJ).trans (hv' T σ z J hJ)⟩

theorem Rep.eq_one (hL : L.IsLB) (hY : Function.Surjective Y.hom.appTop.hom) (h : Rep L Y F v)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), F U h = 1) (e : 𝟙_ (Over S) ⟶ Y)
    (he : ∀ z J, Good L z J → v _ e z J = 1) (T : Over S) (σ : T ⟶ Y) (z : T.left) (J) (hJ : Good L z J) :
    v T σ z J = 1 := by
  obtain ⟨K, _, φ, ε, t, ht, hF', hv⟩ := h
  refine (hv T σ z J hJ).symm.trans ((gen_unique' hL (fun U _ k => ?_) Y.hom e.left (Over.w e) hY ht
    (LB.isGen_oneGen L) (fun y I hI => (hv _ e y I hI).trans ((he y I hI).trans (val_one _).symm)) _ σ.left z J hJ).trans
    (val_one _))
  rw [hF', hF]
  exact Fintype.prod_empty _

end Rep

section Quad
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

abbrev quadφ (w : G ⟶ G) : Fin 4 → (G.left ⟶ G.left) :=
  ![(𝟙 G * w).left, 𝟙 G.left, w.left, (1 : G ⟶ G).left]

def postHom {H : Over S} [GrpObj H] (i : H ⟶ G) [IsMonHom i] (T : Over S) : (T ⟶ H) →* (T ⟶ G) :=
  MonoidHom.mk' (· ≫ i) fun _ _ => MonObj.mul_comp _ _ _

def QuadId (P : CP G) (w : G ⟶ G) (u : LB.Gen (LB.LinComb P.L.L (quadφ w) ![1, -2, -1, 2])) : Prop :=
  ∀ (T : Over S) (z : T.left) (J), Good P.L.L z J →
    (∀ x y v : T ⟶ G, cubeDefect (cubV P.c z J) (fun p => val u p.left z J) x y v (x ≫ w) (y ≫ w) (v ≫ w) = 1) ∧
    ∀ x : T ⟶ G, evenDefect (fun p : T ⟶ G => val P.sym p.left z J) (fun p => val u p.left z J) x (x ≫ w) = 1

variable {H : Over S} [GrpObj H] [IsCommMonObj H] {P : CP G} {i : H ⟶ G} [IsMonHom i]

end Quad

section DVR
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  [Smooth G.hom] [IsSeparated G.hom] [GeometricallyConnected G.hom]

end DVR

end GlobalTheory.EvenCub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfIsWtZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem unit_ext_of_flat {Y Z : Scheme.{0}} (π : Y ⟶ Z) [Flat π] [Surjective π] {V : Z.Opens} {a b : Γ(Z, V)ˣ}
    (h : ∀ y, π y ∈ V → gm π y V a = gm π y V b) : a = b := by
  have e : pullU π V a = pullU π V b := Geo.Tor.unit_ext fun y hy => by
    have k := h y hy
    rw [← Category.id_comp π] at k
    exact (gm_pull (𝟙 Y) π y V hy a).trans (k.trans (gm_pull (𝟙 Y) π y V hy b).symm)
  exact Units.ext (FunDescent.app_injective π V (congrArg Units.val e))

theorem TQ.exists_unit_of_isWt_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (V : Q.B.left.Opens) (f : Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ) (hf : IsWt Q.i _ f.val 0) :
    ∃ a : Γ(Q.B.left, V)ˣ, pullU Q.q.left V a = f := by
  have := Q.q_affine
  obtain ⟨-, h₂, h₃⟩ := invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj inferInstance
    Q.isKernel V
  obtain ⟨a, ha⟩ := h₃ f.val fun Z t g k₁ k₂ => by
    rw [hf Z t g k₁ k₂, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]
  obtain ⟨b, rfl⟩ := h₂ a (ha ▸ f.isUnit)
  exact ⟨b, Units.ext ha⟩

theorem lbIso_of_genWt : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] (Q : TQ G X) (N N' : LB Q.B.left) (u : LB.Gen (N.pull Q.q.left)) (u' : LB.Gen (N'.pull Q.q.left)) (χ : X), N.IsLB → N'.IsLB → Q.GenWt N u χ → Q.GenWt N' u' χ → LBIso N N' := by
  intro S X _ G _ Q N N' u u' χ _ _ hu hu'
  have := Q.q_flat
  have := Q.q_surj
  have key : ∀ (k : N'.ι) (j : N.ι), ∃ a : Γ(Q.B.left, N'.U k ⊓ N.U j)ˣ, ∀ y, Q.q.left y ∈ N'.U k ⊓ N.U j →
      gm Q.q.left y _ a = gm (𝟙 _) y _ (u'.s fun _ => k) * (gm (𝟙 _) y _ (u.s fun _ => j))⁻¹ := by
    intro k j
    have l₁ : Q.q.left ⁻¹ᵁ (N'.U k ⊓ N.U j) ≤ (N'.pull Q.q.left).U fun _ => k := fun _ hx => mem_pull.2 hx.1
    have l₂ : Q.q.left ⁻¹ᵁ (N'.U k ⊓ N.U j) ≤ (N.pull Q.q.left).U fun _ => j := fun _ hx => mem_pull.2 hx.2
    have w := ((hu'.2 fun _ => k).res l₁).mul ((hu.2 fun _ => j).inv.res l₂)
    rw [add_neg_cancel] at w
    obtain ⟨a, ha⟩ := Q.exists_unit_of_isWt_zero _ (res l₁ (u'.s _) * res l₂ (u.s _)⁻¹) w
    refine ⟨a, fun y hy => ?_⟩
    have e := gm_pull (𝟙 _) Q.q.left y _ hy a
    rw [Category.id_comp] at e
    rw [← e, ha, map_mul, gm_res (𝟙 _) y l₁ hy, gm_res (𝟙 _) y l₂ hy, map_inv]
  choose a ha using key
  have tr : ∀ (M : LB Q.B.left) (t : LB.Gen (M.pull Q.q.left)), t.IsGen → ∀ (i i' : M.ι) (y : G.left),
      Q.q.left y ∈ M.U i → Q.q.left y ∈ M.U i' →
      gm (𝟙 _) y _ (t.s fun _ => i) = gm Q.q.left y _ (M.g i i') * gm (𝟙 _) y _ (t.s fun _ => i') := by
    intro M t ht i i' y hi hi'
    have hm : y ∈ (M.pull Q.q.left).U (fun _ => i) ⊓ (M.pull Q.q.left).U (fun _ => i') :=
      ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
    have e := congrArg (gm (𝟙 _) y _) (ht (fun _ => i) (fun _ => i'))
    rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g M Q.q.left (𝟙 _) y _ _ hm.1 hm.2, Category.id_comp] at e
    exact e
  refine ⟨⟨fun p => a p.1 p.2⟩, fun p p' => unit_ext_of_flat Q.q.left fun y hy => ?_⟩
  have e₁ := (gm_res Q.q.left y inf_le_left hy (a p.1 p.2)).trans (ha _ _ y hy.1)
  have e₂ := (gm_res Q.q.left y inf_le_right hy (a p'.1 p'.2)).trans (ha _ _ y hy.2)
  have e₃ : gm Q.q.left y _ ((LB.div N' N).g p p') =
      gm Q.q.left y _ (N'.g p.1 p'.1) * (gm Q.q.left y _ (N.g p.2 p'.2))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) ((map_inv _ _).trans (congrArg _ (gm_res _ y _ hy _))))
  refine e₁.trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) e₃ e₂)).symm)
  rw [tr N' u' hu'.1 p.1 p'.1 y hy.1.1 hy.2.1, tr N u hu.1 p.2 p'.2 y hy.1.2 hy.2.2,
    mul_inv, _root_.mul_mul_mul_comm]

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfOnto
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpansionCriterion

private lemma sum_smul_sum_smul_eq_sum_mul_smul {K S J : Type} [Field K] {Λ : J → Type} [∀ j, CommRing (Λ j)]
    (ρ : ∀ j, K →+* Λ j) (f : S → ∀ j, Λ j) {n : ℕ} (b t : Fin n → S)
    (D : Matrix (Fin n) (Fin n) K) (hD : ∀ k j, f (t k) j = ∑ i, ρ j (D k i) * f (b i) j)
    (c : Fin n → K) (j : J) :
    ∑ k, ρ j (c k) * f (t k) j = ∑ i, ρ j (Matrix.vecMul c D i) * f (b i) j := by
  simp only [hD, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem total_of_onto {K S V J : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    {Λ : J → Type} [∀ j, CommRing (Λ j)] (ρ : ∀ j, K →+* Λ j) (f : S → ∀ j, Λ j)
    (E : S → V → Prop) {n : ℕ} (hn : Module.finrank K V = n) (b : Fin n → S)
    (hb₁ : ∀ c : Fin n → K, ∃ s : S, ∀ j, f s j = ∑ i, ρ j (c i) * f (b i) j)
    (hb₂ : ∀ s : S, ∃ c : Fin n → K, ∀ j, f s j = ∑ i, ρ j (c i) * f (b i) j)
    (hlin : ∀ (t : Fin n → S) (F : Fin n → V) (c : Fin n → K) (s : S), (∀ i, E (t i) (F i)) →
      (∀ j, f s j = ∑ i, ρ j (c i) * f (t i) j) → E s (∑ i, c i • F i))
    (hfun : ∀ s F F', E s F → E s F' → F = F')
    (hon : ∀ F, ∃ s, E s F) (s : S) : ∃ F, E s F := by
  classical

  let v := Module.finBasisOfFinrankEq K V hn
  choose t ht using fun k => hon (v k)
  choose D hD using fun k => hb₂ (t k)
  have key := sum_smul_sum_smul_eq_sum_mul_smul ρ f b t (D : Matrix (Fin n) (Fin n) K) hD

  have hinj : Function.Injective (Matrix.vecMulLinear (D : Matrix (Fin n) (Fin n) K)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hc' : Matrix.vecMul c (D : Matrix (Fin n) (Fin n) K) = 0 := hc
    obtain ⟨s₀, hs₀⟩ := hb₁ 0
    have h1 : E s₀ (∑ k, c k • v k) :=
      hlin t (fun k => v k) c s₀ ht (fun j => by rw [key c j, hc', hs₀ j])
    have h0 : E s₀ (∑ k, (0 : Fin n → K) k • v k) :=
      hlin t (fun k => v k) 0 s₀ ht (fun j => by rw [hs₀ j]; simp)
    have hsum : ∑ k, c k • v k = 0 := by simpa using hfun _ _ _ h1 h0
    funext k
    exact Fintype.linearIndependent_iff.mp v.linearIndependent c hsum k
  obtain ⟨a, ha⟩ := hb₂ s
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) a
  have hc' : Matrix.vecMul c (D : Matrix (Fin n) (Fin n) K) = a := hc
  exact ⟨_, hlin t (fun k => v k) c s ht (fun j => by rw [key c j, hc']; exact ha j)⟩

noncomputable def scalRes {R : Type} [CommRing R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) : R →+* Γ(Y, W) :=
  ((Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp p.appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem expBij_of_onto : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → Module.Finite (FractionRing R) (Fam D.toPre (FractionRing R) k) → Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) = k ^ A.g → (∀ F : Fam D.toPre (FractionRing R) k, ∃ s : U.SecK k, U.Expands k s F) → U.ExpBij k := by
  intro hS R _ _ I hR D A G _ _ _ U k hk _ hrank honto
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hS R I D A G U k hk
  have resTop_scal_lemma_2 : ∀ (W : (pullback G.hom (jK R)).Opens) (r : FractionRing R),
      resTop W (scal (pullback.snd G.hom (jK R)) r) = scalRes (pullback.snd G.hom (jK R)) W r :=
    fun W r => (GlobalTheory.ExpandsLinear.scalOn_apply _ W r).trans rfl

  have huniq := GlobalTheory.T.uniformisation_eq_iff_expansion_eq R I hR D A G U k
  have htot : ∀ s : U.SecK k, ∃ F, U.Expands k s F := by
    intro s
    refine total_of_onto (K := FractionRing R) (f := fun (s : U.SecK k) j => s.f j)
      (ρ := fun j => scalRes (pullback.snd G.hom (jK R)) _) (E := U.Expands k) hrank b
      (fun c => ?_) (fun s => ?_) (fun t F c s ht hs => ?_)
      (fun s F F' h h' => (huniq s s F F' h h').mp rfl) honto s
    · obtain ⟨s, hs⟩ := hb₁ c
      exact ⟨s, fun j => by simpa only [resTop_scal_lemma_2] using hs j⟩
    · obtain ⟨c, hc, _⟩ := hb₂ s
      exact ⟨c, fun j => by simpa only [resTop_scal_lemma_2] using hc j⟩
    · exact GlobalTheory.expands_linear R I hR D A G U k _ t F c s ht
        (fun j => by simpa only [resTop_scal_lemma_2] using hs j)

  refine ⟨fun s => ?_, fun F => ?_⟩
  · obtain ⟨F, hF⟩ := htot s
    exact ⟨F, hF, fun F' hF' => (huniq s s F' F hF' hF).mp rfl⟩
  · obtain ⟨s, hs⟩ := honto F
    exact ⟨s, hs, fun s' hs' => (huniq s' s F F hs' hs).mpr rfl⟩

end GlobalTheory.ExpansionCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfExpBij
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finrank_fam_of_expBij : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → U.ExpBij k → Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) = k ^ A.g := by
  intro hBC R _ _ I hadm D A G _ _ _ U k hk hbij
  obtain ⟨b, hex, huniq⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hBC R I D A G U k hk
  choose F hF using fun i => (hbij.1 (b i)).exists
  have hlin := fun c s hs => GlobalTheory.expands_linear R I hadm D A G U k (k ^ A.g) b F c s hF hs
  let φ : (Fin (k ^ A.g) → FractionRing R) →ₗ[FractionRing R] Fam D.toPre (FractionRing R) k :=
    Fintype.linearCombination (FractionRing R) F
  have hφ : ∀ c, φ c = ∑ i, c i • F i := fun c => rfl
  have hinj : Function.Injective φ := by
    intro c c' h
    obtain ⟨s, hs⟩ := hex c
    obtain ⟨s', hs'⟩ := hex c'
    have h1 := hlin c s hs
    have h2 := hlin c' s' hs'
    rw [← hφ] at h1 h2
    rw [← h] at h2
    have e : s = s' := (hbij.2 (φ c)).unique h1 h2
    subst e
    exact (huniq s).unique hs hs'
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨s, hs⟩ := (hbij.2 x).exists
    obtain ⟨c, hc⟩ := (huniq s).exists
    exact ⟨c, (hbij.1 s).unique (hlin c s hc) hs⟩
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open scoped TensorProduct in

theorem flat_SpecMap_of_flat_localization_maximal (V : Type) [CommRing V] (C : CommRingCat.{0})
    (f : CommRingCat.of V ⟶ C)
    (h : ∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd (Spec.map f)
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m)))))) :
    Flat (Spec.map f) := by
  rw [Flat.SpecMap_iff]
  letI : Algebra V C := f.hom.toAlgebra
  have key : Module.Flat V C := by
    refine Module.flat_of_isLocalized_maximal V C (fun P _ => Localization.AtPrime P ⊗[V] C)
      (fun P _ => TensorProduct.mk V (Localization.AtPrime P) C 1) fun P _ => ?_
    have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct V (Localization.AtPrime P) C)).flip
    have h1 := h P
    have h2 := sq.isoPullback_hom_snd
    have h3 : Flat (sq.isoPullback.hom ≫ pullback.snd _ _) := by
      haveI : Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V C)))
        (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime P))))) := h1
      infer_instance
    rw [h2, Flat.SpecMap_iff] at h3
    haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[V] C) :=
      RingHom.flat_algebraMap_iff.mp h3
    exact Module.Flat.trans V (Localization.AtPrime P) _
  exact key

theorem flat_of_isFinite_of_flat_localization_maximal :
    ∀ (V : Type) [CommRing V] (H : Over (Sp V)), IsFinite H.hom → (∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd H.hom (spMap (algebraMap V (Localization.AtPrime m))))) → Flat H.hom := by
  intro V _ H hfin h
  haveI : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨f, hf⟩ := Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)
  have hf' : H.hom = H.left.isoSpec.hom ≫ Spec.map f := by rw [hf]; simp
  have : Flat (Spec.map f) := by
    refine flat_SpecMap_of_flat_localization_maximal V _ f fun m _ => ?_
    have h1 := h m
    rw [hf, ← pullbackRightPullbackFstIso_inv_snd_snd]
    haveI : Flat (pullback.snd H.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m))))) := h1
    infer_instance
  rw [hf']
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericFibreCardTorsionCubicalPairingPerfect
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem card_and_nondeg_of_pullback (hL : Laws) {S S' : Scheme.{0}} [IsLocallyNoetherian S'] (f : S' ⟶ S)
    (A : PolAV S') {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) (φ : A.A.left ⟶ G.left)
    (hφ : IsPullback φ A.A.hom G.hom f)
    (mul : ∀ (T : Over S') (x y : T ⟶ A.A), toBase hφ.w (x * y) = toBase hφ.w x * toBase hφ.w y)
    (hw : LBIso A.L (P.L.L.pull φ)) {F : Type} [Field F] [IsAlgClosed F] (q : Spec (CommRingCat.of F) ⟶ S')
    {N : ℕ} (h1 : 1 ≤ N) (hN : (N : F) ≠ 0) :
    Nat.card {x : Over.mk (q ≫ f) ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧
      ∀ x : Over.mk (q ≫ f) ⟶ G, x ^ N = 1 →
        (∀ y : Over.mk (q ≫ f) ⟶ G, y ^ N = 1 → CubWeil P.c N x y 1) → x = 1 := by
  haveI := A.isAb.comm
  obtain ⟨w, hg⟩ := hw
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, hm⟩ := exists_isCPMap P mul A.L A.isLB w hg
  let β : (Over.mk q ⟶ A.A) →* (Over.mk (q ≫ f) ⟶ G) := toBaseHom mul (Over.mk q)
  have hβ : ∀ y, (β y).left = y.left ≫ φ := fun y => rfl
  have inj : Function.Injective β := fun a b e => Over.OverMorphism.ext (hφ.hom_ext
    ((hβ a).symm.trans ((congrArg CommaMorphism.left e).trans (hβ b))) ((Over.w a).trans (Over.w b).symm))
  have surj : Function.Surjective β := fun x =>
    ⟨Over.homMk (hφ.lift x.left q (Over.w x)) (hφ.lift_snd _ _ _),
      Over.OverMorphism.ext ((hβ _).trans (hφ.lift_fst _ _ _))⟩
  have hp : ∀ y, y ^ N = 1 ↔ β y ^ N = 1 := fun y => by
    rw [← map_pow, ← map_one β, inj.eq_iff]
  refine ⟨?_, fun x hx h => ?_⟩
  · rw [← (hL.mulN S' A N h1).2.2.2.2 F q hN]
    exact (Nat.card_congr ((Equiv.ofBijective β ⟨inj, surj⟩).subtypeEquiv hp)).symm
  · obtain ⟨x, rfl⟩ := surj x
    have hx' := (hp x).2 hx
    rw [GlobalTheory.ThetaRep.eq_one_of_weilIs hL A q hN x hx' fun y hy => ?_, map_one]
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil c hx' hy
    have e := (cubWeil_map _ _ f G A.A P ⟨_, c, s, h₁, h₂, h₃⟩ φ _ w hm N (Over.mk q) x y ζ hζ).unique (h _ ((hp y).1 hy))
    exact (cubWeil_iff_weilIs hL.globalFns A.isAb hx' hy 1).1 (e ▸ hζ)

theorem generic_card_and_nondeg : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → Nat.card {x : TF (R := V) F ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧ ∀ x : TF (R := V) F ⟶ G, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ G, y ^ N = 1 → CubWeil s.P.c N x y 1) → x = 1 := by
  intro hL V _ _ _ A G _ _ s F _ _ _ N h1
  haveI := s.gen_hom
  haveI : CharZero V := s.cdvr.2.2
  haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap (FractionRing V) F).injective
  let φ : A.A.left ⟶ G.left := s.gen.inv.left ≫ pullback.fst G.hom (jK V)
  haveI : IsIso s.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map s.gen.inv))
  have hφ : IsPullback φ A.A.hom G.hom (jK V) := by
    have a : IsPullback s.gen.inv.left A.A.hom (pullback.snd G.hom (jK V)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w s.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using a.paste_horiz (IsPullback.of_hasPullback G.hom (jK V))
  refine card_and_nondeg_of_pullback hL (jK V) A s.P φ hφ (fun T x y => ?_) ?_ (jFK F) h1
    (Nat.cast_ne_zero.2 (by omega))
  · have e : ∀ a : T ⟶ A.A, toBase hφ.w a = toBase (A := G) (A' := (Over.pullback (jK V)).obj G)
        (g := pullback.fst G.hom (jK V)) pullback.condition (a ≫ s.gen.inv) := fun a =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, e, e, MonObj.mul_comp, toBase_mul_pullback]
  · exact LBIso.chartPull (chartPullSec A.L s.gen.hom.left s.gen.inv.left
      (congrArg CommaMorphism.left s.gen.inv_hom_id)) (chartPullSame s.P.L.L _ _ _ _ fun _ => rfl) ⟨s.wA, s.wA_gen⟩

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem isProper_of_isProjBy :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), IsProjBy f → IsProper f := by
  intro R _ X f h
  obtain ⟨N, φ, hφ, e⟩ := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver (R := R) f).1 h
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  rw [← e]
  infer_instance

end GlobalTheory.AbLaw
end

