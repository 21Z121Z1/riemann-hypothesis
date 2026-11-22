import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemFinsetInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ESecStruct
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TripleProductPointCompProjection
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace WCub

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem clause_iff {T XB XG E : Scheme.{0}} {K : Type} [Fintype K] (mB : T ⟶ XB) (mG : T ⟶ XG) (p : K → (T ⟶ E))
    (UB : XB.Opens) (UG : XG.Opens) (W : K → E.Opens) (a : Γ(XB, UB)ˣ) (b : Γ(XG, UG)ˣ) (c : ∀ k, Γ(E, W k)ˣ)
    (ε : K → ℤ) :
    (∀ (V : T.Opens) (hB : V ≤ mB ⁻¹ᵁ UB) (hG : V ≤ mG ⁻¹ᵁ UG) (hw : ∀ k, V ≤ p k ⁻¹ᵁ W k),
      res hB (pullU mB UB a) = (∏ k, res (hw k) (pullU (p k) (W k) (c k)) ^ ε k) * res hG (pullU mG UG b)) ↔
    ∀ y : T, mB y ∈ UB → mG y ∈ UG → (∀ k, p k y ∈ W k) →
      gm mB y UB a = (∏ k, gm (p k) y (W k) (c k) ^ ε k) * gm mG y UG b := by
  have one : ∀ {X : Scheme.{0}} (m : T ⟶ X) (U : X.Opens) (V : T.Opens) (h : V ≤ m ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (y : T),
      y ∈ V → gm (𝟙 T) y V (res h (pullU m U u)) = gm m y U u := fun m U V h u y hy =>
    (gm_res (𝟙 T) y h hy _).trans ((gm_pull (𝟙 T) m y U (h hy) u).trans (by rw [Category.id_comp]))
  have key : ∀ (V : T.Opens) (hG : V ≤ mG ⁻¹ᵁ UG) (hw : ∀ k, V ≤ p k ⁻¹ᵁ W k) (y : T), y ∈ V →
      gm (𝟙 T) y V ((∏ k, res (hw k) (pullU (p k) (W k) (c k)) ^ ε k) * res hG (pullU mG UG b)) =
        (∏ k, gm (p k) y (W k) (c k) ^ ε k) * gm mG y UG b := fun V hG hw y hy =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
      (map_zpow _ _ _).trans (congrArg (· ^ ε k) (one _ _ V _ _ y hy)))) (one _ _ V _ _ y hy))
  constructor
  · intro H y hB hG hw
    let V : T.Opens := mB ⁻¹ᵁ UB ⊓ mG ⁻¹ᵁ UG ⊓ ⟨⋂ k, (p k ⁻¹ᵁ W k : Set T), isOpen_iInter_of_finite fun k =>
      (p k ⁻¹ᵁ W k).isOpen⟩
    have hy : y ∈ V := ⟨⟨hB, hG⟩, Set.mem_iInter.2 hw⟩
    have l : ∀ k, V ≤ p k ⁻¹ᵁ W k := fun k z hz => Set.mem_iInter.1 hz.2 k
    have e := congrArg (gm (𝟙 T) y V) (H V (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) l)
    exact (one _ _ V _ _ y hy).symm.trans (e.trans (key V _ _ y hy))
  · intro H V hB hG hw
    exact unit_ext fun y hy => (one _ _ V _ _ y hy).trans ((H y (hB hy) (hG hy) fun k => hw k hy).trans
      (key V _ _ y hy).symm)

section Cube

variable {S S' : Scheme.{0}} {G : Over S} (f : S' ⟶ S) {E T : Over S'} (p : (Over.map f).obj E ⟶ G)
  (x : Fin 3 → (T ⟶ E))

abbrev tri : T.left ⟶ (G3 G).left :=
  (lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p))).left

theorem tripleProductPoint_comp_projection (i : Fin 3) : tri f p x ≫ (x3 G i).left = (x i).left ≫ p.left := by
  have : lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p)) ≫
      x3 G i = (Over.map f).map (x i) ≫ p := by
    fin_cases i <;> simp [x3]
  exact congrArg (fun q => q.left) this

theorem tri_thφ [GrpObj G] [IsCommMonObj G] [GrpObj E] [IsCommMonObj E] (q : E ⟶ (Over.pullback f).obj G)
    [IsMonHom q] (hp : p.left = q.left ≫ pullback.fst G.hom f) (k : thK) :
    tri f p x ≫ thφ G (x3 G) k = (psum E x k.down).left ≫ p.left := by
  have h := isGrpPullback_pullback G f
  have e₁ := psum_push h (fun i => x i ≫ q) (x3 G)
    (lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p)))
    (fun i => Over.OverMorphism.ext (by
      refine Eq.trans ?_ (tripleProductPoint_comp_projection f p x i).symm
      rw [hp]
      exact Category.assoc _ _ _)) k.down
  have e₂ := psum_hom (MonoidHom.mk' (fun z : T ⟶ E => z ≫ q) fun a b => MonObj.mul_comp a b q) x k.down
  refine e₁.symm.trans ?_
  rw [hp, ← Category.assoc]
  exact congrArg (fun z => z.left ≫ pullback.fst G.hom f) e₂.symm

end Cube

theorem alg {U K : Type} [CommGroup U] [Fintype K] (ε : K → ℤ) (a b c d : K → U) (h : ∀ k, a k * b k = c k * d k)
    {tM tM' tL tL' : U} (e₁ : tM = (∏ k, a k ^ ε k) * tM') (e₂ : tM = (∏ k, c k ^ ε k) * tL)
    (e₃ : tL = (∏ k, d k ^ ε k) * tL') : tM' = (∏ k, b k ^ ε k) * tL' := by
  have : (∏ k, a k ^ ε k) * (∏ k, b k ^ ε k) = (∏ k, c k ^ ε k) * (∏ k, d k ^ ε k) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← mul_zpow, ← mul_zpow, h]
  apply mul_left_cancel (a := ∏ k, a k ^ ε k)
  rw [← e₁, e₂, e₃, ← _root_.mul_assoc, ← _root_.mul_assoc, this]

end WCub

open ReciprocityTheory.ChartRestriction.G.Geo.Tor WCub in
set_option maxHeartbeats 1600000 in

theorem w_cub_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain
    R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD
    : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A'
    : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj
    G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc
    : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U
    : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst
    G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf
    φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit)
    (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w'
    : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt'
    e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt'
    e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG
    I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt'
    e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst
    D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe
    x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe
    x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I'
    e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL'
    : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e
    G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w'
    e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫
    (fstG I' e G').left) z jL jL')) → ∀ (hgp : Geo.Tor.IsGrpPullback G' G (specOf φ) (bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) (c' : CubicalStr G' L'), Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ
    G (x3 G)) thε c'.t U.cubG.t (Geo.Tor.cubeMapOf hgp).F3 → ∀ (e : ℕ) (T : Over (Spec
    (CommRingCat.of (R' ⧸ I' ^ (e + 1))))) (x : Fin 3 → (T ⟶ thickObj R' I' e G')) (jL
    : thK → L'.L.ι) (jM : thK → D'.toPre.P.L.ι), LB.Coh L'.L (fun k => (lift ((Over.map (thick R' I'
    e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ≫ thφ G' (x3
    G') k) jL → LB.Coh D'.toPre.P.L (fun k => (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt'
    e).pG) (lift ((Over.map (thick R' I' e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map
    (x 2) ≫ (gt' e).pG))).left ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) jM → ∀ (V : T.left.Opens) (hB
    : V ≤ (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt' e).pG) (lift ((Over.map (thick R' I'
    e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map (x 2) ≫ (gt'
    e).pG))).left ⁻¹ᵁ (Theta D'.toPre.P.A D'.toPre.P.L).U jM) (hG : V ≤ (lift ((Over.map (thick R'
    I' e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ⁻¹ᵁ (Theta G' L'.L).U jL) (hw
    : ∀ k : thK, V ≤ (psum (thickObj R' I' e G') x k.down).left ⁻¹ᵁ ((D'.toPre.P.L.pull (gt'
    e).pG.left).U (fun _ => jM k) ⊓ (L'.L.pull (fstG I' e G').left).U
    (fun _ => jL k))), res hB (pullU _ _ (D'.toPre.cub.t.s jM)) = (∏ k : thK, res (hw k) (pullU
    (psum (thickObj R' I' e G') x k.down).left _ ((w' e).s
    (fun _ => jM k, fun _ => jL k))) ^ thε k) * res hG (pullU _ _ (c'.t.s jL)) := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ _ U L' wL _ _ _ gt' w' _ _ H hgp c' hc e T x jL' jM' _ cM
  obtain ⟨h, h₁, ⟨h₂, -⟩, sq⟩ := H e
  have hgB := pull_grp hD
  have := (gt' e).q_hom
  have := (U.gt e).q_hom
  have mt : Mono (thick R I e) := by
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have mf : Mono (fstG I e G).left := inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))
  have hs : ∀ i, ((x i).left ≫ h ≫ (thickObj R I e G).hom) ≫ thick R I e = T.hom ≫ thick R' I' e ≫ specOf φ := by
    intro i
    have a₁ : (thickObj R I e G).hom ≫ thick R I e = (fstG I e G).left ≫ G.hom := (Over.w (fstG I e G)).symm
    have a₂ : (fstG I' e G').left ≫ G'.hom = (thickObj R' I' e G').hom ≫ thick R' I' e := Over.w (fstG I' e G')
    have a₃ := hgp.1.w
    rw [Category.assoc, Category.assoc, a₁, ← Category.assoc h, h₁, Category.assoc, a₃, ← Category.assoc _ G'.hom, a₂,
      ← Over.w (x i), Category.assoc, Category.assoc]
  let T₀ : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk ((x 0).left ≫ h ≫ (thickObj R I e G).hom)
  let x₀ : Fin 3 → (T₀ ⟶ thickObj R I e G) := fun i => Over.homMk ((x i).left ≫ h) (by
    rw [← cancel_mono (thick R I e)]
    exact ((congrArg (· ≫ thick R I e) (Category.assoc _ _ _)).trans (hs i)).trans (hs 0).symm)
  have f₁ := tri_thφ (thick R' I' e) (fstG I' e G') x (𝟙 _) (Category.id_comp _).symm
  have f₂ := tri_thφ (thick R' I' e) (gt' e).pG x (gt' e).q rfl
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x₀ (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x₀ (U.gt e).q rfl
  have g₁ : tri (thick R' I' e) (fstG I' e G') x ≫ (cubeMapOf hgp).F3 = tri (thick R I e) (fstG I e G) x₀ :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, tripleProductPoint_comp_projection, tripleProductPoint_comp_projection, Category.assoc]
      exact (congrArg ((x i).left ≫ ·) h₁.symm).trans (Category.assoc _ _ _).symm
  have g₂ : tri (thick R' I' e) (gt' e).pG x ≫ (cubeMapOf hgB).F3 = tri (thick R I e) (U.gt e).pG x₀ :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, tripleProductPoint_comp_projection, tripleProductPoint_comp_projection, Category.assoc]
      exact (congrArg ((x i).left ≫ ·) h₂).trans (Category.assoc _ _ _).symm
  have k₁ : ∀ k : thK, (tri (thick R' I' e) (fstG I' e G') x ≫ thφ G' (x3 G') k) ≫ (cubeMapOf hgp).F =
      tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k := fun k => by
    rw [← g₁, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((cubeMapOf hgp).psum_comm k.down)
  have k₂ : ∀ k : thK, (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F =
      tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k := fun k => by
    rw [← g₂, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((cubeMapOf hgB).psum_comm k.down)
  have ph : ∀ k : thK, (psum (thickObj R I e G) x₀ k.down).left = (psum (thickObj R' I' e G') x k.down).left ≫ h :=
    fun k => by
      rw [← cancel_mono (fstG I e G).left]
      refine (f₃ k).symm.trans ((k₁ k).symm.trans ?_)
      rw [f₁ k, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) h₁.symm
  refine (clause_iff (tri (thick R' I' e) (gt' e).pG x) (tri (thick R' I' e) (fstG I' e G') x)
    (fun k : thK => (psum (thickObj R' I' e G') x k.down).left) _ _ _ (D'.toPre.cub.t.s jM') (c'.t.s jL')
    (fun k => (w' e).s (fun _ => jM' k, fun _ => jL' k)) thε).2 fun y hB hL hw => ?_
  obtain ⟨J', hJ', eJ'⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB y _ jM' cM (fun k => Set.mem_iInter.1 hB k)
  choose J hJ using fun χ : T.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
  choose N hN using fun χ : T.left ⟶ G.left => exists_chart U.LG.isLB (χ y)
  let jM : thK → D.toPre.P.L.ι := fun k => J (tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)
  let jL : thK → U.LG.L.ι := fun k => N (tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k)
  have mM : ∀ k, (tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k) y ∈ D.toPre.P.L.U (jM k) :=
    fun k => hJ _
  have mL : ∀ k, (tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k) y ∈ U.LG.L.U (jL k) := fun k => hN _
  have e₂ := (clause_iff (tri (thick R I e) (U.gt e).pG x₀) (tri (thick R I e) (fstG I e G) x₀)
    (fun k : thK => (psum (thickObj R I e G) x₀ k.down).left) _ _ _ (D.toPre.cub.t.s jM) (U.cubG.t.s jL)
    (fun k => (U.w e).s (fun _ => jM k, fun _ => jL k)) thε).1
    (U.w_cub e T₀ x₀ jL jM (fun a b e => congrArg N e) (fun a b e => congrArg J e)) y
    (Set.mem_iInter.2 mM) (Set.mem_iInter.2 mL) (fun k => ⟨mem_pull.2 (by
      have := mM k; rw [f₄ k] at this; exact this), mem_pull.2 (by
      have := mL k; rw [f₃ k] at this; exact this)⟩)
  have mL' : ∀ k, ((tri (thick R' I' e) (fstG I' e G') x ≫ thφ G' (x3 G') k) ≫ (cubeMapOf hgp).F) y ∈
      U.LG.L.U (jL k) := fun k => by rw [k₁ k]; exact mL k
  have mM' : ∀ k, ((tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F) y ∈
      D.toPre.P.L.U (jM k) := fun k => by rw [k₂ k]; exact mM k
  have e₃ := hc _ (tri (thick R' I' e) (fstG I' e G') x) y jL jL' mL' (fun k => Set.mem_iInter.1 hL k)
  rw [g₁] at e₃
  have e₁ := cub_pull hG hD (T' := (Over.map (thick R' I' e)).obj T) (z := y) (J := J) (J' := J') hJ hJ'
    ((Over.map (thick R' I' e)).map (x 0) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map (x 1) ≫ (gt' e).pG)
    ((Over.map (thick R' I' e)).map (x 2) ≫ (gt' e).pG)
  have v₁ : val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
      (tri (thick R' I' e) (gt' e).pG x ≫ (cubeMapOf hgB).F3) y J =
      gm (tri (thick R I e) (U.gt e).pG x₀) y (LB.wchart _ (thφ D.toPre.P.A (x3 D.toPre.P.A)) jM)
        (D.toPre.cub.t.s jM) := by
    rw [g₂]; rfl
  have v₂ := val_of (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
    (tri (thick R' I' e) (gt' e).pG x) y J' jM' eJ'
  refine alg thε (fun k => gw hD.w ((psum (thickObj R' I' e G') x k.down).left ≫ (gt' e).pG.left) y (jM k) (jM' k))
    (fun k => gw (w' e) (psum (thickObj R' I' e G') x k.down).left y (jM' k) (fun _ => jL' k))
    (fun k => gw (U.w e) ((psum (thickObj R' I' e G') x k.down).left ≫ h) y (jM k) (fun _ => jL k))
    (fun k => gw wL ((psum (thickObj R' I' e G') x k.down).left ≫ (fstG I' e G').left) y (jL k) (jL' k))
    (fun k => sq _ _ y _ _ _ _ ?_ (mem_pull.1 (hw k).1) ?_ (mem_pull.1 (hw k).2))
    (v₁.symm.trans (e₁.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) v₂)))
    (e₂.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) rfl))
    (e₃.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) rfl))
  · have := mM' k
    rw [f₂ k] at this
    exact this
  · have := mL' k
    rw [f₁ k] at this
    exact this
  · show gw hD.w (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) y
      (J ((tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F))
      (J' (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k)) = _
    rw [k₂ k, eJ' k, f₂ k]
  · rw [← ph k]; rfl
  · rw [f₁ k]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEqIffExpansionEq
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpansionFunction

open FieldBaseChange

theorem eq_iff_comb_eq_zero {R : Type} [CommRing R] [IsDomain R] {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ}
    (π : Y ⟶ Spec (CommRingCat.of R)) (π' : Y' ⟶ Spec (CommRingCat.of (FractionRing R))) {p : Y' ⟶ Y}
    (hp : p ≫ π = π' ≫ jK R) (hφ : ∀ k, φ' k = p ≫ φ k) (hinj : ∀ W : Y.Opens, Function.Injective (p.app W))
    (π₀ : Y' ⟶ Spec (CommRingCat.of R)) (h₀ : π₀ = π' ≫ jK R)
    {s s' : LB.Sec (LB.LinComb L φ' ε)} {σ σ' : LB.Sec (LB.LinComb L φ ε)} {r r' : R} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (H : GeneratorPullback.SecScal L φ' ε s φ ε σ p (scal π₀ r)) (H' : GeneratorPullback.SecScal L φ' ε s' φ ε σ' p (scal π₀ r')) :
    s = s' ↔ ∀ j, ∑ i : Fin 2, resTop _ (scal π (![r', -r] i)) * (![σ, σ'] i).f j = 0 := by
  let t : SecOver π' (LB.LinComb L φ' ε) := s
  let t' : SecOver π' (LB.LinComb L φ' ε) := s'
  let τ : SecOver π (LB.LinComb L φ ε) := σ
  let τ' : SecOver π (LB.LinComb L φ ε) := σ'
  have E : pullOver L ε hp hφ τ = algebraMap R (FractionRing R) r • t :=
    (secScal_iff hp hφ hL t τ π₀ _ h₀ r).1 H
  have E' : pullOver L ε hp hφ τ' = algebraMap R (FractionRing R) r' • t' :=
    (secScal_iff hp hφ hL t' τ' π₀ _ h₀ r').1 H'
  have hi : ∀ x : SecOver π (LB.LinComb L φ ε), pullOver L ε hp hφ x = 0 → x = 0 := fun x hx =>
    SecOver.ext _ _ fun j => hinj _ (by
      have e := congrArg (chartFun π' _ j) hx
      have hw := wchart_eq (L := L) hφ j
      refine Geo.Tor.fn_ext fun y hy => ?_
      have hy' : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L φ' j := hw.ge hy
      have e₂ := congrArg (Geo.Tor.gs (𝟙 Y') y (LB.wchart L φ' j)) e
      refine (Geo.Tor.gs_pull _ p y _ hy _).trans ((gs_pullFn hp hw.le _ (𝟙 Y') y hy').symm.trans
        (e₂.trans ((gs_zero' _ y _ hy').trans ?_)))
      exact ((Geo.Tor.gs_pull _ p y _ hy _).trans (gs_zero' (𝟙 Y' ≫ p) y (LB.wchart L φ j) hy)).symm)
  have ha : algebraMap R (FractionRing R) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr
  have ha' : algebraMap R (FractionRing R) r' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr'
  have key : pullOver L ε hp hφ (r' • τ + (-r) • τ') =
      (algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) r') • (t - t') := by
    rw [map_add, map_smulₛₗ, map_smulₛₗ, E, E', map_neg, smul_smul, smul_smul, smul_sub, sub_eq_add_neg,
      ← neg_smul, neg_mul, mul_comm (algebraMap R (FractionRing R) r')]
  have main : t = t' ↔ r' • τ + (-r) • τ' = 0 := by
    constructor
    · intro h
      exact hi _ (by rw [key, h, sub_self, smul_zero])
    · intro h
      rw [h, map_zero] at key
      exact sub_eq_zero.1 ((smul_eq_zero_iff_right (mul_ne_zero ha ha')).1 key.symm)
  refine main.trans ⟨fun h j => ?_, fun h => SecOver.ext _ _ fun j => ?_⟩
  · rw [Fin.sum_univ_two]
    exact congrArg (chartFun π _ j) h
  · have := h j
    rw [Fin.sum_univ_two] at this
    exact this

end ExpansionFunction

theorem eq_iff_expansion_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (s s' : U.SecK k) (F F' : Fam D.toPre (FractionRing R) k), U.Expands k s F → U.Expands k s' F' → (s = s' ↔ F = F') := by
  intro R _ _ I hR D A G _ _ hG U k s s' F F' ⟨r, hr, σ, f, hσ, hf, hE⟩ ⟨r', hr', σ', f', hσ', hf', hE'⟩
  have := U.smooth
  have := D.toPre.P.isAb.smooth
  have : Flat G.hom := inferInstance
  have : Flat D.toPre.P.A.hom := inferInstance
  have e : (TF (R := R) (FractionRing R)).hom = jK R := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have hd : IsDominant (TF (R := R) (FractionRing R)).hom := DVR.GC.isDominant_jFR (V := R) (FractionRing R)
  have h₁ : IsSchemeTheoreticallyDominant (TF (R := R) (FractionRing R)).hom := .of_isDominant _
  have h₂ : IsSchemeTheoreticallyDominant (jK R) := e ▸ h₁
  have h₅ : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have h₃ : QuasiCompact (TF (R := R) (FractionRing R)).hom := e ▸ h₅
  have h₄ : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  have hs := ExpansionFunction.eq_iff_comb_eq_zero U.LG.isLB G.hom (pullback.snd G.hom (jK R))
    pullback.condition (fun _ => (Category.comp_id _).symm) (pullback.fst G.hom (jK R)).app_injective _ rfl
    hr hr' hσ hσ'
  have hw : (DegPre.BF D.toPre (FractionRing R)).hom =
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R := by
    rw [← e]; exact (Over.w _).symm
  have hF := fun α => ExpansionFunction.eq_iff_comb_eq_zero D.toPre.P.isLB D.toPre.P.A.hom
    (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left
    ((Over.w (DegPre.prB D.toPre (FractionRing R))).trans hw) (DVR.GC.famφ_eq D.toPre (FractionRing R) α)
    (pullback.snd (TF (R := R) (FractionRing R)).hom D.toPre.P.A.hom).app_injective _ hw hr hr' (hf α) (hf' α)
  have H := comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k 2 ![r', -r] ![σ, σ'] ![f, f']
    (fun i => by fin_cases i; exacts [hE, hE'])
  have hc : ∀ α (i : Fin 2), (![f, f'] i) α = ![f α, f' α] i := fun α i => by fin_cases i <;> rfl
  simp only [hc] at H
  constructor
  · intro h
    exact DVR.fam_ext fun α j => by rw [(hF α).2 (H.1 (hs.1 h) α)]
  · intro h
    exact hs.2 (H.2 hG fun α => (hF α).1 (by rw [h]))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfLevels
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoordLinear

open Geo.Tor

theorem fn_eq_of_levels {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of R), W))
    (h : ∀ e, ((thick R I e).app W).hom a = ((thick R I e).app W).hom b) : a = b := by
  subst hW
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (((thick R I e).app ⊤).hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

theorem val_eq_of_levels {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsHausdorff I R] {X : Scheme.{0}}
    {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ e y J, Good M y J → val u (thick R I e) y J = val u' (thick R I e) y J)
    (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hM hF u hu
  choose j hj using fun k => exists_chart hM (φ' k (IsLocalRing.closedPoint R))
  have hW : LB.wchart M φ' j = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff (R := R) (LB.wchart M φ' j)).1 (Set.mem_iInter.2 hj)
  have hm : ∀ y, y ∈ LB.wchart M φ' j := fun y => by rw [hW]; trivial
  have e : t.s j = u'.s j := by
    refine Units.ext (fn_eq_of_levels I _ hW _ _ fun e => ?_)
    refine congrArg Units.val (show pullU (thick R I e) _ (t.s j) = pullU (thick R I e) _ (u'.s j) from
      unit_ext fun y _ => ?_)
    choose I₀ hI₀ using fun χ : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ X => exists_chart hM (χ y)
    refine (gm_pull _ _ y _ (hm _) _).trans (Eq.trans ?_ (gm_pull _ _ y _ (hm _) _).symm)
    rw [Category.id_comp]
    exact (gen_trans ht _ y (hm _) (Good.mem hI₀ φ' _)).trans
      ((congrArg _ ((hv _ _ y I₀ hI₀).trans (h e y I₀ hI₀))).trans (gen_trans hu' _ y (hm _) (Good.mem hI₀ φ' _)).symm)
  refine (hv Z r z J hJ).symm.trans ?_
  exact (gen_trans ht r z (hJ.mem φ' r) (hm _)).trans
    ((congrArg (fun q => _ * gm r z _ q) e).trans (gen_trans hu' r z (hJ.mem φ' r) (hm _)).symm)

theorem prod_gtT {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (DVR.cP D _ χ * b).left)⁻¹ * h (DVR.cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (DVR.cP D _ χ * b).left ^ (-1 : ℤ) * h (DVR.cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem level_ext {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) {G : Over (Spec (CommRingCat.of R))}
    {Z : Scheme.{0}} {p p' : Z ⟶ (thickObj R I e G).left}
    (h : p ≫ (fstG I e G).left = p' ≫ (fstG I e G).left) : p = p' := by
  have h' : p ≫ pullback.fst G.hom (thick R I e) = p' ≫ pullback.fst G.hom (thick R I e) := h
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact (cancel_mono (pullback.fst G.hom (thick R I e))).1 h'

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG → ∀ (a : O) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp gp' : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (x ≫ ιG.act a) ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp'.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp'.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp g → GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp' g' → Geo.Tor.GtAct ιD a g g' := by
  intro hG R _ _ _ I hI _ D A G _ _ U O _ _ _ ιD ιA ιG hlin a x gp gp' h h' F _ _ g g' hg hg'
  have : IsAdicComplete I R := hI.2.2.2
  choose xe hx hb hs using h
  choose xe' hx' hb' hs' using h'
  have hxe : ∀ e, (xe' e).left = (xe e).left ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left := fun e =>
    level_ext I e ((congrArg (·.left) (hx' e)).trans (Eq.symm ((Category.assoc _ _ _).trans
      ((congrArg (fun q => (xe e).left ≫ q) (DVR.fstG_act I e (ιG.act a))).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ (ιG.act a).left) (hx e)).trans
          (Category.assoc _ _ _)))))))
  have hB : gp'.b = gp.b ≫ ιD.onB.act a := by
    ext1
    refine GlobalTheory.hom_ext_of_isHausdorff I fun e => ?_
    refine (congrArg (·.left) (hb' e)).symm.trans ?_
    refine (congrArg (fun q => q ≫ (U.gt e).pG.left) (hxe e)).trans ((Category.assoc _ _ _).trans ?_)
    refine (congrArg (fun q => (xe e).left ≫ q) (DVR.pG_act U hlin e a)).trans ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (fun q => q.left ≫ (ιD.onB.act a).left) (hb e)).trans (Category.assoc _ _ _)
  have hgb : g.b = toUnit _ ≫ gp.b := Over.OverMorphism.ext hg.1
  have hgb' : g'.b = toUnit _ ≫ gp'.b := Over.OverMorphism.ext hg'.1
  refine ⟨by rw [hgb, hgb', hB, Category.assoc], fun u hu hu₀ χ => corr_of_val D.toPre.P.isLB fun y J hJ => ?_⟩
  have E : ∀ (T : Over (Spec (CommRingCat.of R))) (b : T ⟶ D.toPre.P.A), b = toUnit T ≫ gp.b →
      (lift (toUnit T ≫ D.toPre.c χ) b).left = (toUnit T).left ≫ (lift (DVR.cP D.toPre _ χ) gp.b).left := by
    rintro T b rfl
    rw [← Over.comp_left, comp_lift, DVR.cP, ← Category.assoc, comp_toUnit]
  have key := val_eq_of_levels I D.toPre.P.isLB (K := Fin 4 ⊕ Fin 6) (K' := Fin 4)
    (u := LB.mulGen D.toPre.P.L _ _ _ _ (gp.s (star a • χ))
      (LB.pullGen D.toPre.P.L _ _ u (lift (DVR.cP D.toPre _ χ) gp.b).left)) (u' := gp'.s χ)
    (fun V _ h => by
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := V) _ (prod_gtT gp.b (star a • χ) h)
        (prod_ros _ _ (DVR.cP D.toPre _ χ) gp.b h)).trans (Eq.trans ?_ (prod_gtT gp'.b χ h).symm)
      have hc : DVR.cP D.toPre (𝟙_ _) (star a • χ) = DVR.cP D.toPre _ χ ≫ ιD.onB.act (star a) := by
        rw [DVR.cP, ιD.c_lin, ← Category.assoc]; rfl
      rw [hc, hB]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp.isGen _) (DVR.pullGen_isGen _ _ _ _ hu _)) (gp'.isGen χ)
    (fun e z J hJ => by
      have H := val_corr hJ (TLinPf.tLin_of hG R I O D A G U ιD ιA ιG hlin e a u hu hu₀ χ) (xe e).left
      have H₁ := val_corr hJ (hs e (star a • χ)) (𝟙 _)
      have H₂ := val_corr hJ (hs' e χ) (𝟙 _)
      rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at H₁ H₂
      rw [val_mul hJ, val_pull hJ, val_pull hJ, ← hxe, H₁, H₂] at H
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg _ ((val_pull hJ _ _ _).trans ?_)) H)
      have E' : xe e ≫ lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG = lift (toUnit _ ≫ D.toPre.c χ) (xe e ≫ (U.gt e).pG) := by
        rw [comp_lift, ← Category.assoc, comp_toUnit]
      exact congrArg (fun q => val u q z J) ((congrArg (·.left) E').trans (E _ _ (hb e))).symm)
    _ (toUnit (TF (R := R) F)).left y J hJ
  have H₁ := val_corr hJ (hg.2 (star a • χ)) (𝟙 _)
  have H₂ := val_corr hJ (hg'.2 χ) (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at H₁ H₂
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (((val_mul hJ _ _ _).symm.trans key).trans H₂.symm))
  refine congrArg₂ (· * ·) H₁ ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  exact congrArg (fun q => val u q y J) ((Category.id_comp _).trans (E _ _ hgb))

end GlobalTheory.CoordLinear
end

