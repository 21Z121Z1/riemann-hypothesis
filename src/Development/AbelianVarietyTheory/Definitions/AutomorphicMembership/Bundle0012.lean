import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RestrictLineBundleSymmetryUnitsEquivIsoApply
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullRigIsSymmetric
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomComb

section Generators

variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]

def combGen (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) : LB.Gen (LB.LinComb (LB.LinComb L F δ) φ ε) where
  s := fun jj => ∏ i, res (GeneratorPullback.box_le L F φ jj i) ((t i).s (fun k _ => jj k i)) ^ δ i

theorem gm_combGen (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (r : Z ⟶ Y) (z : Z)
    (jj : K → (LB.LinComb L F δ).ι) (h : r z ∈ LB.wchart (LB.LinComb L F δ) φ jj) :
    gm r z (LB.wchart (LB.LinComb L F δ) φ jj) ((combGen L F δ φ ε t).s jj) =
      ∏ i, gm r z (LB.wchart (L.pull (F i)) φ (fun k _ => jj k i)) ((t i).s (fun k _ => jj k i)) ^ δ i :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ δ i) (gm_res r z _ h _)))

theorem trF_comb (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (jj jj' : K → (LB.LinComb L F δ).ι) (h : r z ∈ LB.wchart (LB.LinComb L F δ) φ jj)
    (h' : r z ∈ LB.wchart (LB.LinComb L F δ) φ jj') :
    trF (L := LB.LinComb L F δ) φ ε r z jj jj' =
      ∏ i, trF (L := L.pull (F i)) φ ε r z (fun k _ => jj k i) (fun k _ => jj' k i) ^ δ i := by
  unfold trF
  simp only [← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (congrArg (· ^ ε k) (gm_linComb L F δ (r ≫ φ k) z (jj k) (jj' k) (Set.mem_iInter.1 h k)
    (Set.mem_iInter.1 h' k))).trans ?_
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← zpow_mul, mul_comm, zpow_mul]
  refine congrArg (fun q => (q ^ ε k) ^ δ i) ?_
  exact (gm_pull_g L (F i) (r ≫ φ k) z (fun _ => jj k i) (fun _ => jj' k i)
    (Set.mem_iInter.1 (GeneratorPullback.box_le L F φ jj i h) k) (Set.mem_iInter.1 (GeneratorPullback.box_le L F φ jj' i h') k)).symm

theorem isGen_combGen (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (combGen L F δ φ ε t).IsGen := by
  refine isGen_of_gm _ fun y jj jj' h h' => ?_
  rw [gm_combGen L F δ φ ε t (𝟙 Y) y jj h, gm_combGen L F δ φ ε t (𝟙 Y) y jj' h', trF_comb L F δ φ ε (𝟙 Y) y jj jj' h h',
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← mul_zpow]
  exact congrArg (· ^ δ i) (gen_trans (ht i) (𝟙 Y) y (GeneratorPullback.box_le L F φ jj i h) (GeneratorPullback.box_le L F φ jj' i h'))

variable {L}

theorem good_factor {F : J → (X' ⟶ X)} {δ : J → ℤ} {z : Z} {I : (Z ⟶ X') → (LB.LinComb L F δ).ι}
    (hI : Good (LB.LinComb L F δ) z I) (i : J) : Good (L.pull (F i)) z (fun χ _ => I χ i) :=
  fun χ => mem_pull.2 (Set.mem_iInter.1 (hI χ) i)

theorem val_combGen {F : J → (X' ⟶ X)} {δ : J → ℤ} {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (r : Z ⟶ Y) {z : Z} {I : (Z ⟶ X') → (LB.LinComb L F δ).ι}
    (hI : Good (LB.LinComb L F δ) z I) :
    val (combGen L F δ φ ε t) r z I = ∏ i, val (t i) r z (fun χ _ => I χ i) ^ δ i :=
  gm_combGen L F δ φ ε t r z _ (hI.mem φ r)

end Generators

theorem isCub_prod {B U J : Type} [CommGroup B] [CommGroup U] [Fintype J] (θ : J → B → B → B → U)
    (h : ∀ i, IsCub (θ i)) (δ : J → ℤ) : IsCub fun x y z => ∏ i, θ i x y z ^ δ i where
  face x y := Finset.prod_eq_one fun i _ => by rw [(h i).face, one_zpow]
  s01 x y z := Finset.prod_congr rfl fun i _ => by rw [(h i).s01]
  s12 x y z := Finset.prod_congr rfl fun i _ => by rw [(h i).s12]
  coc x x' x'' y := by
    simp only [← Finset.prod_mul_distrib, ← mul_zpow]
    exact Finset.prod_congr rfl fun i _ => by rw [(h i).coc]

variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
  {J : Type} [Fintype J]

def pullRig (L : RigLB G) (f : A ⟶ G) [IsMonHom f] : RigLB A :=
  (CubeMap.ofHom f).rigLB L (LB.isLB_linComb L.isLB _ _)
    (LBxP.isGen_pullAlong L.L f.left (𝟙 _) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec A)
      (fun _ => (CubeMap.ofHom f).e_comm) L.rig L.rigGen)

def pullCub {L : RigLB G} (c : CubicalStr G L) (f : A ⟶ G) [IsMonHom f] : CubicalStr A (pullRig L f) :=
  CubePf.cubical (CubeMap.ofHom f) L c _ _

theorem pullRig_isSymmetric {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) (f : A ⟶ G) [IsMonHom f] :
    (pullRig L f).IsSymmetric := by
  obtain ⟨_, _, -, h⟩ := proved_CubePullSt S S G A (CubeMap.ofHom f) L c
  exact h hs

variable (u : J → (A ⟶ G)) [∀ i, IsMonHom (u i)] (δ : J → ℤ)

def combRig (L : RigLB G) : RigLB A where
  L := LB.LinComb L.L (fun i => (u i).left) δ
  rig := combGen L.L (fun i => (u i).left) δ (fun _ : PUnit => eSec A) (fun _ => 1) fun i => (pullRig L (u i)).rig
  isLB := LB.isLB_linComb L.isLB _ _
  rigGen := isGen_combGen _ _ _ _ _ _ fun i => (pullRig L (u i)).rigGen

def combCub {L : RigLB G} (c : CubicalStr G L) : CubicalStr A (combRig u δ L) :=
  CubTransport.cubicalOfVal (L := combRig u δ L)
    (combGen L.L (fun i => (u i).left) δ (thφ A (x3 A)) thε fun i => (pullCub c (u i)).t)
    (isGen_combGen _ _ _ _ _ _ fun i => (pullCub c (u i)).isGen) fun T z I hI => by
      have h := isCub_prod _ (fun i => isCub_cubV (pullCub c (u i)) (T := T) (good_factor hI i)) δ
      convert h using 4 with x y w
      exact val_combGen (fun i => (pullCub c (u i)).t) _ hI

theorem isSymmetric_iff (L : RigLB G) : L.IsSymmetric ↔ ∃ sy, BoxCompare.IsCanonSym L.L sy := by
  refine ⟨fun ⟨_, w, h⟩ => ?_, fun ⟨sy, h⟩ => ⟨GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv, _, (BoxCompare.isNormSymm_iff L sy).2 h⟩⟩
  obtain ⟨sy, rfl⟩ := (BoxCompare.symEquiv L.L _).surjective w
  exact ⟨sy, (BoxCompare.isNormSymm_iff L sy).1 h⟩

theorem combRig_isSymmetric {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) :
    (combRig u δ L).IsSymmetric := by
  choose sy hsy using fun i => (isSymmetric_iff _).1 (pullRig_isSymmetric c hs (u i))
  refine (isSymmetric_iff _).2 ⟨combGen L.L (fun i => (u i).left) δ _ _ sy,
    isGen_combGen _ _ _ _ _ _ fun i => (hsy i).1, corr_of_val (combRig u δ L).isLB fun y I hI => ?_⟩
  refine (val_pull hI _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  refine (val_combGen sy _ hI).trans (Finset.prod_eq_one fun i _ => ?_)
  have e := (val_pull (good_factor hI i) (sy i) (eSec A) (𝟙 _)).symm.trans
    ((val_corr (good_factor hI i) (hsy i).2 (𝟙 _)).trans (val_one _))
  exact (congrArg (· ^ δ i) e).trans (one_zpow _)

end GlobalTheory.HomComb
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SplitFacTwistRight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.ThModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem nonempty_tow (D : D7) : Nonempty (Tow D) := GlobalTheory.Mem.Th.nonempty_tow (GlobalTheory.WittLow.wittLowEx D)

theorem orthEx (D : D7) : OrthEx D := by
  intro V hV
  obtain ⟨b, hb⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (two_ne_zero : (2 : D.host.E) ≠ 0) V.rank V.hT.flip
    (fun x y => V.herm.eq y x) V.rank_eq
  have ho : ∀ i j, i ≠ j → V.hT (b i) (b j) = 0 := fun i j hij => hb j i hij.symm
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.FockBasisMatrix.basis_matrix D V).2 b
  have hd : ∀ τ, ((V.frame.toMatrix b).map (tauE D τ)).det ≠ 0 := fun τ => by
    have := (tauE D τ).map_det (V.frame.toMatrix b)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (h1.map (tauE D τ)).ne_zero
  choose A hA hA' using fun τ => GlobalTheory.MonomialDiag.exists_monomial _ _ _ (gramAt D V τ) _ _ (hV (tauE D τ)) (hd τ)
    (h3 ho τ).1 (h3 ho τ).2.1
  exact ⟨A, V.frame.toMatrix b, hA, h1, fun i j hij => (h2 i j).trans (ho i j hij), hA'⟩

theorem nonempty_orthDec (D : D7) : Nonempty (OrthDec D) := GlobalTheory.Mem.Th.nonempty_orthDec (orthEx D)

theorem om_rational {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χ χ' : IdC D}
    {om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (h : IsWeilOn ψ V W χ χ' om)
    {γ : GA D V} (hγ : γ ∈ GQ V) {δ : GA D W} (hδ : δ ∈ GQ W) (Φ Φ' : ThS ψ V W) (w : WA V W)
    (e : Φ'.1 = Heisenberg₂ ψ V W w Φ.1) : (om (γ, δ) Φ).1 (actHom V W γ δ w) = Φ.1 w := by
  have h0 : ∀ u : WA V W, symplH V W 0 u = 0 := fun u => by
    simp [symplH, sympl, hHom]
  have h1 := congrFun (h.Heisenberg₂ γ δ w Φ Φ' e) 0
  rw [h.aut γ hγ δ hδ, e] at h1
  simpa [Heisenberg₂, h0] using h1.symm

theorem root_of_at {e d : AE D} (hd : d * cA D d = 1)
    (hs : (e + cA D e) * (d - 1) = d - 1) :
    e * d + (1 - e) = d * cA D (e * d + (1 - e)) := by
  rw [map_add, map_mul, map_sub, map_one]
  have h1 : d * (cA D e * cA D d + (1 - cA D e)) = cA D e * (d * cA D d) + d - d * cA D e := by ring
  rw [h1, hd]
  linear_combination hs

theorem splitFac_twist_right {V W : HSp D} (h : V.rank ≠ W.rank) (χ χ' ν : IdC D) (x y : (AE D)ˣ) :
    splitFac V W χ (χ' * ν) x y = (if V.rank < W.rank then (ν x)⁻¹ else ν x) * splitFac V W χ χ' x y := by
  unfold splitFac
  by_cases k : V.rank < W.rank
  · rw [if_pos k.le, if_pos k.le, if_pos k, MonoidHom.mul_apply, _root_.mul_inv_rev, mul_assoc]
  · have k' : ¬ V.rank ≤ W.rank := by omega
    rw [if_neg k', if_neg k', if_neg k, MonoidHom.mul_apply, mul_comm (χ' x), mul_assoc]

theorem splitFac_twist_left {V W : HSp D} (h : V.rank ≠ W.rank) (χ χ' ν : IdC D) (x y : (AE D)ˣ) :
    splitFac V W (χ * ν) χ' x y = (if V.rank < W.rank then ν y else (ν y)⁻¹) * splitFac V W χ χ' x y := by
  unfold splitFac
  by_cases k : V.rank < W.rank
  · rw [if_pos k.le, if_pos k.le, if_pos k, MonoidHom.mul_apply, mul_comm (χ y), mul_left_comm]
  · have k' : ¬ V.rank ≤ W.rank := by omega
    rw [if_neg k', if_neg k', if_neg k, MonoidHom.mul_apply, _root_.mul_inv_rev, mul_left_comm]

end GlobalTheory.Mem.ThModel

end
end

