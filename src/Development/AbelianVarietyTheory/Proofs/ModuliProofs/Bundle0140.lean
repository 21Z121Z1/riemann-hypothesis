import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem cubV_of_pmaps {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f) {L : RigLB G} {L' : RigLB G'}
    {c : CubicalStr G L} {c' : CubicalStr G' L'} {w : LB.Iso L'.L (L.L.pull m.F)}
    (H : PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t m.F3) {T : Over S'} {z : T.left} {J J'}
    (hJ : Good L.L z J) (hJ' : Good L'.L z J') (a b d : T ⟶ G') :
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := Over.mk (T.hom ≫ f)) z J (Out.toBase hw a) (Out.toBase hw b)
      (Out.toBase hw d)) =
      (∏ I : thK.{0}, (fun q => gw w q z (J (q ≫ m.F)) (J' q)) ((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ^ thε I) *
        cubV c' z J' a b d := by
  have co : ∀ i : Fin 3, m.F3 ≫ (x3 G i).left = (x3 G' i).left ≫ m.F := fun i => by
    have h := m.psum_comm {i}
    rw [psum_single, psum_single] at h
    exact h.symm
  have q : (lift a (lift b d)).left ≫ m.F3 =
      (lift (Out.toBase hw a) (lift (Out.toBase hw b) (Out.toBase hw d))).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, co, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  have e := H _ (lift a (lift b d)).left z (fun I => J (((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ≫ m.F))
    (fun I => J' ((lift a (lift b d)).left ≫ thφ G' (x3 G') I)) (fun I => hJ _) (fun I => hJ' _)
  refine Eq.trans ?_ e
  refine (congrArg (fun r => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t r z J) q.symm).trans ?_
  refine val_of _ _ _ _ _ fun I => congrArg J ?_
  rw [Category.assoc, Category.assoc]
  exact congrArg _ (m.psum_comm I.down).symm

theorem cubWeil_of_isPullCubical : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y) → ∀ (L : RigLB G) (L' : RigLB G') (c : CubicalStr G L) (c' : CubicalStr G' L'), m.IsPullCubical c' c → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil c' N x y ζ → CubWeil c N (Out.toBase hw x) (Out.toBase hw y) ζ := by
  intro S S' f G _ _ G' _ _ m hw mul L L' c c' h N T x y ζ hζ
  obtain ⟨w, -, -, H⟩ := (isPullCubical_iff m c c').1 h
  let β := toBaseHom mul T
  refine ⟨(map_pow β x N).symm.trans ((congrArg β hζ.1).trans (map_one β)),
    (map_pow β y N).symm.trans ((congrArg β hζ.2.1).trans (map_one β)), fun z J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_pt L'.isLB (Z := T.left) z
  obtain ⟨W, hW⟩ : ∃ W : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ,
    W = fun q => gw w q z (J (q ≫ m.F)) (J' q) := ⟨_, rfl⟩
  let θ : (Over.mk (T.hom ≫ f) ⟶ G) → (Over.mk (T.hom ≫ f) ⟶ G) → (Over.mk (T.hom ≫ f) ⟶ G) →
    (T.left.presheaf.stalk z)ˣ := cubV c (T := Over.mk (T.hom ≫ f)) z J
  have a' : ∀ a b d : T ⟶ G', θ (β a) (β b) (β d) * W (a * b).left * W (a * d).left * W (b * d).left *
      W (1 : T ⟶ G').left = W (a * b * d).left * W a.left * W b.left * W d.left * cubV c' z J' a b d := by
    intro a b d
    have e := (cubV_of_pmaps m hw H (T := T) (z := z) hJ hJ' a b d).trans (congrArg₂ (· * ·)
      ((congrArg (fun V : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ =>
        ∏ I : thK.{0}, V ((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ^ thε I) hW.symm).trans (prod_cub a b d W)) rfl)
    have e' : θ (β a) (β b) (β d) = _ := e
    rw [e']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact cubN_ratio_twist β (fun x => W x.left) a' hζ.1 hζ.2.1 (hζ.2.2 z J' hJ')

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.Direct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelDirect

open GlobalTheory.SiegelPullComp

private theorem tensor_left_hom_ext' {T : Scheme.{0}} {G : Over T} {X : Scheme.{0}} (a b : X ⟶ (G ⊗ G).left)
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := by
  have hw : b ≫ (G ⊗ G).hom = a ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), reassoc_of% h1]
  have key := CartesianMonoidalCategory.hom_ext
    (Over.homMk a rfl : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G) (Over.homMk b hw)
    (by ext; simpa using h1) (by ext; simpa using h2)
  simpa using congrArg (fun k => k.left) key

theorem exists_inverse {T : Scheme.{0}} {A G : Over T} [GrpObj A] [GrpObj G] {φ : A.left ⟶ G.left}
    {φ₂ : (G2 A).left ⟶ (G2 G).left} (hφ : IsGrpPullback A G (𝟙 T) φ) (hs : Geo.Tor.IsSquare φ φ₂) :
    ∃ (F : G.left ⟶ A.left) (F₂ : (G2 G).left ⟶ (G2 A).left), IsGrpPullback G A (𝟙 T) F ∧ Geo.Tor.IsSquare F F₂ ∧
      φ ≫ F = 𝟙 _ ∧ F₂ ≫ φ₂ = 𝟙 _ := by
  have hw : φ ≫ G.hom = A.hom := by simpa using hφ.1.w
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  let e : A ≅ G := Over.isoMk (asIso φ) hw
  have heL : e.inv.left = inv φ := rfl
  have hsF : Geo.Tor.IsSquare (inv φ) (e.inv ⊗ₘ e.inv).left := by
    constructor
    · rw [← Over.comp_left, tensorHom_fst, Over.comp_left, heL]
    · rw [← Over.comp_left, tensorHom_snd, Over.comp_left, heL]
  refine ⟨inv φ, (e.inv ⊗ₘ e.inv).left, ⟨?_, ?_⟩, hsF, by simp, ?_⟩
  · refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← hw]
    simp
  · intro U x y x₀ y₀ hx hy
    have key := hφ.2 (Over.mk (U.hom ≫ 𝟙 T)) x₀ y₀ (Over.homMk x.left (by simp))
      (Over.homMk y.left (by simp)) (by simp [hx]) (by simp [hy])
    have hxy := mul_left_congr (a := (U.hom ≫ 𝟙 T) ≫ 𝟙 T) (b := U.hom) (by simp)
      (Over.homMk x.left (by simp)) (Over.homMk y.left (by simp)) x y (by simp) (by simp)
    rw [hxy.symm.trans key]
    simp
  · apply tensor_left_hom_ext'
    · rw [Category.assoc, hs.1, ← Category.assoc, hsF.1]
      simp
    · rw [Category.assoc, hs.2, ← Category.assoc, hsF.2]
      simp

theorem direct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T : Scheme.{0}) (sT : T ⟶ Sp O) (t : SAB H T) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), SiegData sT t lev Ag z bas w → ∃ (θ : t.G.left ⟶ Ag.univ.A.left) (θ₂ : (G2 t.G).left ⟶ (G2 Ag.univ.A).left), IsGrpPullback t.G Ag.univ.A (w ≫ pullback.fst _ _) θ ∧ IsSquare θ θ₂ ∧ LBIso (abelian₂ t.G t.PP.L) (Ag.univ.P.pull θ₂) ∧ ∀ u, (lev (bas u)).left ≫ θ = (w ≫ pullback.fst _ _) ≫ (Ag.univ.lev u).left := by
  intro E _ _ _ H D O _ T sT t lev g p N Ag z bas w hd
  obtain ⟨o, φ, φ₂, hφ, hs, hL, hlev, hcl, ψ, ψ₂, hψ, hs', hP, hlev'⟩ := hd
  obtain ⟨F, F₂, hF, hsF, hφF, hF₂⟩ := exists_inverse hφ hs
  have h0 : t.PP.L.IsLB := t.PP.isLB
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := by
    unfold abelian₂
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ h0 _ _
  refine ⟨F ≫ ψ, F₂ ≫ ψ₂, (hF.comp hψ).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hs'.1, ← Category.assoc, hsF.1, Category.assoc]
  · rw [Category.assoc, hs'.2, ← Category.assoc, hsF.2, Category.assoc]
  · have hΛ₁ := pull_isLB hΛ (𝟙 (G2 t.G).left)
    have hΛ₂ := pull_isLB (pull_isLB hΛ φ₂) F₂
    have hO := pull_isLB o.isLB F₂
    have hU₁ := pull_isLB (pull_isLB Ag.univ.isLB ψ₂) F₂
    have hU₂ := pull_isLB Ag.univ.isLB (F₂ ≫ ψ₂)
    have s1 : LBIso (abelian₂ t.G t.PP.L) ((abelian₂ t.G t.PP.L).pull (𝟙 _)) := iso_pull_id hΛ
    have s2 : LBIso ((abelian₂ t.G t.PP.L).pull (𝟙 _)) (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) := by
      have k := iso_pull_pull hΛ φ₂ F₂
      rw [hF₂] at k
      exact k.symm
    have s3 : LBIso (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) (o.P.pull F₂) := (iso_pull F₂ hL).symm
    have s4 : LBIso (o.P.pull F₂) ((Ag.univ.P.pull ψ₂).pull F₂) := iso_pull F₂ hP
    have s5 : LBIso ((Ag.univ.P.pull ψ₂).pull F₂) (Ag.univ.P.pull (F₂ ≫ ψ₂)) := iso_pull_pull Ag.univ.isLB ψ₂ F₂
    exact LBIso.trans hΛ hΛ₁ hU₂ s1 (LBIso.trans hΛ₁ hΛ₂ hU₂ s2
      (LBIso.trans hΛ₂ hO hU₂ s3 (LBIso.trans hO hU₁ hU₂ s4 s5)))
  · intro u
    rw [← hlev u]
    simp only [Category.assoc, reassoc_of% hφF]
    exact hlev' u

end GlobalTheory.SiegelDirect

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOnTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullRigid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_of_field (hS : Out.SerreSt) {S : Scheme.{0}} {t : SAB H S} (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) {K : Type} [Field K] [CharZero K] {z : Sp K ⟶ S}
    {t' : SAB H (Sp K)} (m m' : SABMap t' t z) {N : ℕ} (hN : 3 ≤ N)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Sp K) (y : Over.mk x ⟶ t'.G),
      y ^ N = 1 → y.left ≫ m.φ = y.left ≫ m'.φ) : m.φ = m'.φ := by
  obtain ⟨θ, hθ, hφ, -, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w₁, g₁, -⟩ := m.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hc)).mpr trivial
  have : ConnectedSpace t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  let P : Out.PolAV (Sp K) :=
    { A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB
      ample := relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) U hU hy hA
      ktriv := kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) hK
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have hNK : IsUnit (N : K) := (Nat.cast_ne_zero.2 (by omega)).isUnit
  have hMu : IsUnit (N : Γ(Sp K, ⊤)) := by
    simpa using hNK.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : Etale (Out.mulA t'.G N).left := GrpTangent.etale_id_pow t'.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine hS (Sp K) P N hN θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric t'.G N θ.hom fun k _ _ x y hy => ?_)
    · obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (t'.G.hom ⁻¹ᵁ ⊤).ι
      refine gen_chartPull (chartPullOut t'.PP.L _ _ _ _ fun n => ?_) t ht
      fin_cases n
      exacts [rfl, (Category.comp_id _).symm]
    · let β : K →+* k := (Spec.preimage x).hom
      have : CharZero k := (RingHom.charZero_iff β.injective).1 inferInstance
      apply Over.OverMorphism.ext
      apply m'.cart.1.hom_ext
      · rw [Over.comp_left, Category.assoc]
        exact (congrArg _ hφ).trans (hfix k x y hy)
      · rw [Over.w, Over.w]
  rw [← hφ, h, Over.id_left, Category.id_comp]

theorem eq_on_torsion {D : Datum H} {n N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (RZ H n N)} {t : SAB H S}
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {t' : SAB H S'} {f : S' ⟶ S} (ν ν' : SABMap t' t f)
    (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)) (hN : 0 < N) (o : FullObj D s t lev)
    (h : ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) (h' : ∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ t'.G) (hy : y ^ N = 1) :
    y.left ≫ ν.φ = y.left ≫ ν'.φ := by
  obtain ⟨-, I, -, hI⟩ := o.geom k (x ≫ f) (Spec.preimage ((x ≫ f) ≫ s)).hom (Spec.map_preimage _).symm
  have hy₁ : pushHom ν.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := (I.onto N hN _).1 hy₁
  have e : (x ≫ f) ≫ (lev a).left = y.left ≫ ν.φ := congrArg (fun q => q.left) ((hI a).trans ha)
  have e₁ : y.left = x ≫ (lv a).left := by
    apply ν.cart.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h a).trans (h' a).symm)

end GlobalTheory.FullRigid

theorem GlobalTheory.fullObj_rigid : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (t' : SAB H S') (f : S' ⟶ S) (ν ν' : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), 3 ≤ N → Odd N → FullObj D s t lev → IsReduced S' → (∀ x : S', CharZero (S'.residueField x)) → (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → (∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left) → ν.φ = ν'.φ := by
  intro hL E _ _ _ H D n N S S' s t lev t' f ν ν' lv hN _ o _ hc h h'
  obtain ⟨θ, hθ, hφ, -⟩ := sabMap_iso ν ν' rfl rfl
  have hA : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 o.proper, t'.semi.geomConnected⟩
  have key : θ.hom = 𝟙 _ := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre hL.globalFns t'.G hA θ.hom (IsMonHom.one_hom θ.hom) fun p => ?_
    have := hc p
    let j : Sp (S'.residueField p) ⟶ S' := S'.fromSpecResidueField p
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull j t'
    generalize (⟨(Over.pullback j).obj t'.G, IsSemiAbelian.pullback _ t'.G t'.semi,
      OAct.pullback _ t'.G t'.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t'' at m
    obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν m
    obtain ⟨b, hb⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' m
    have e : a.φ = b.φ := GlobalTheory.FullRigid.eq_of_field hL.serre o.proper o.ample o.ktriv a b hN fun k _ _ _ x y hy => by
      have hy₁ : pushHom m.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
      have e₁ := GlobalTheory.FullRigid.eq_on_torsion ν ν' lv (by omega) o h h' k (x ≫ j) _ hy₁
      rw [ha, hb, ← Category.assoc, ← Category.assoc]
      exact e₁
    refine ⟨_, _, j, m.φ, _, (default : PrimeSpectrum (S'.residueField p)),
      Scheme.fromSpecResidueField_apply p _, m.cart.1, ?_⟩
    apply ν'.cart.1.hom_ext
    · rw [Category.assoc]
      exact (congrArg (m.φ ≫ ·) hφ).trans (ha.symm.trans (e.trans hb))
    · rw [Category.assoc, Over.w]
  rw [← hφ, key, Over.id_left, Category.id_comp]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtaleAndSurjectiveOfDensePartMonoFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isOpenImmersion_of_isFinite_of_densePart {U W Z : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian Z] [GlobalTheory.IsNormalScheme Z] (j : U ⟶ W) (g : W ⟶ Z) [IsFinite g]
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] [Flat (j ≫ g)]
    [SurjectiveOnStalks (j ≫ g)] : IsOpenImmersion g := by
  have hη : genericPoint W ∈ genericPoints W := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  let V : Z.Opens := GlobalTheory.IsNormalScheme.component
    ⟨_, irreducibleComponent_mem_irreducibleComponents (g (genericPoint W))⟩
  have hVc : IsClosed (V : Set Z) := GlobalTheory.IsNormalScheme.isClosed_component _
  have : IsIntegral V.toScheme := GlobalTheory.IsNormalScheme.isIntegral_component _
  have hr : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (((genericPoint_spec W).specializes (Set.mem_univ w)).map g.continuous).mem_closed hVc
      mem_irreducibleComponent
  let g' : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hr
  have hg' : g' ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : IsFinite (g' ≫ V.ι) := hg' ▸ inferInstance
  have : IsFinite g' := IsFinite.of_comp g' V.ι
  have hlift : j ≫ g' = IsOpenImmersion.lift V.ι (j ≫ g) (by
      rintro _ ⟨w, rfl⟩
      exact hr ⟨j w, rfl⟩) :=
    IsOpenImmersion.lift_uniq _ _ _ _ (by rw [Category.assoc, hg'])
  have hs : SurjectiveOnStalks ((j ≫ g') ≫ V.ι) := by rw [Category.assoc, hg']; infer_instance
  have : Flat (j ≫ g') := by
    rw [hlift]
    exact MorphismProperty.of_isPullback (P := @Flat)
      (IsOpenImmersion.isPullback_lift_id (j ≫ g) V.ι _).flip ‹Flat (j ≫ g)›
  have : SurjectiveOnStalks (j ≫ g') := SurjectiveOnStalks.of_comp _ V.ι
  have : IsDominant g' := by
    obtain ⟨u', hu', hu''⟩ := Flat.generalizingMap (j ≫ g')
      ((genericPoint_spec V.toScheme).specializes (Set.mem_univ ((j ≫ g') u)))
    refine ⟨?_⟩
    refine Dense.mono (s₁ := {genericPoint V.toScheme}) ?_ ?_
    · rintro _ rfl
      exact ⟨j u', hu''⟩
    · exact dense_iff_closure_eq.mpr (genericPoint_spec V.toScheme)
  have : IsIso (g'.stalkMap (genericPoint W)) := by
    rw [← hu]
    have h := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ≫ g') u
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j u
    rw [Scheme.Hom.stalkMap_comp] at h
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g'.stalkMap (j u)) (j.stalkMap u) _ h
  have := isIso_of_isIntegralHom_of_isIso_stalkMap g' (fun y => inferInstance)
  rw [← hg']
  infer_instance

theorem etale_and_surjective_of_densePart_mono_finiteEtale : ∀ (S S₀ Y Y₀ Z : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian Y] (j : S₀ ⟶ S) (j' : Y₀ ⟶ Y) (e : Y ⟶ S) (e₀ : Y₀ ⟶ S₀) (p : Z ⟶ S) (i : Y₀ ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsFinite e → j' ≫ e = e₀ ≫ j → IsFinite p → Etale p → i ≫ p = e₀ ≫ j → Surjective e₀ → Etale e₀ → Mono i → Etale e ∧ Surjective e := by
  intro S S₀ Y Y₀ Z _ _ j j' e e₀ p i hS hY _ _ _ _ _ _ _ _ _ hj _ _ hi _ _ _
  have hYn := GlobalTheory.IsNormalScheme.of_pred hY
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Z := (isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
      ((isNormalScheme_iff S).mp (GlobalTheory.IsNormalScheme.of_pred hS)))
  obtain ⟨g, ⟨hg₁, hg₂⟩, -⟩ := existsUnique_lift_of_densePart Y Y₀ S Z j' hY ‹_› ‹_› ‹_› ‹_› p e i
    inferInstance (hi.trans hj.symm)
  have : IsFinite (g ≫ p) := hg₂ ▸ inferInstance
  have : IsFinite g := IsFinite.of_comp g p
  let k : Y₀ ⟶ pullback p j := pullback.lift i e₀ hi
  have hk₁ : k ≫ pullback.fst p j = i := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd p j = e₀ := pullback.lift_snd _ _ _
  have : Etale (k ≫ pullback.snd p j) := hk₂ ▸ inferInstance
  have : Etale k := Etale.of_comp k (pullback.snd p j)
  have : Mono (k ≫ pullback.fst p j) := hk₁ ▸ inferInstance
  have : Mono k := mono_of_mono k (pullback.fst p j)
  have : IsOpenImmersion k := IsOpenImmersion.of_flat_of_mono k
  have : Flat i := hk₁ ▸ inferInstance
  have : SurjectiveOnStalks i := hk₁ ▸ inferInstance
  constructor
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) _
      (GlobalTheory.IsNormalScheme.iSup_component Y)]
    intro W
    have : IsDominant (j' ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j'› _
    have h : j' ∣_ GlobalTheory.IsNormalScheme.component W ≫ (GlobalTheory.IsNormalScheme.component W).ι ≫ g =
        (j' ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ i := by
      rw [morphismRestrict_ι_assoc, hg₁]
    have : Flat (j' ∣_ GlobalTheory.IsNormalScheme.component W ≫
        (GlobalTheory.IsNormalScheme.component W).ι ≫ g) := h ▸ inferInstance
    have : SurjectiveOnStalks (j' ∣_ GlobalTheory.IsNormalScheme.component W ≫
        (GlobalTheory.IsNormalScheme.component W).ι ≫ g) := h ▸ inferInstance
    have := isOpenImmersion_of_isFinite_of_densePart (j' ∣_ GlobalTheory.IsNormalScheme.component W)
      ((GlobalTheory.IsNormalScheme.component W).ι ≫ g)
    rw [← hg₂, ← Category.assoc]
    infer_instance
  · have : IsDominant (j' ≫ e) := hj ▸ inferInstance
    have : IsDominant e := IsDominant.of_comp j' e
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, ← e.isClosedMap.isClosed_range.closure_eq]
    exact e.denseRange.closure_range

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompleteDVRPointGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.GenTrait

theorem charZero_functionField (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [CharZero W]
    (f : Sp W ⟶ Z) : CharZero Z.functionField := by
  have h1 : CharZero Γ(Z, ⊤) :=
    RingHom.charZero (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  exact charZero_of_injective_ringHom (Z.germToFunctionField_injective ⊤)

theorem exists_trait_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  intro Z _ W _ _ _ f
  have := charZero_functionField Z W f
  refine ⟨PowerSeries Z.functionField, inferInstance, inferInstance, inferInstance, ?_,
    spMap (algebraMap Z.functionField (PowerSeries Z.functionField)) ≫
      Z.fromSpecStalk (genericPoint Z), fun y => ?_⟩
  · exact ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      algebraRat.charZero _⟩
  · rw [Scheme.Hom.comp_apply]
    have hy : ∀ p : PrimeSpectrum Z.functionField, p = IsLocalRing.closedPoint Z.functionField :=
      fun p => Subsingleton.elim _ _
    exact (congrArg (Z.fromSpecStalk (genericPoint Z)) (hy _)).trans
      Scheme.fromSpecStalk_closedPoint

end GlobalTheory.GenTrait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalDerivationOfKodairaSpencerZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory

theorem exists_locDer_top_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∃ d, LocDer P₀.A.hom p m D ⊤ d := by
  intro hL P₀ u Hm χ hu R _ x₀ X p m hp hpb D s hD hs
  have key : ∀ (W : X.Opens) (f : Γ(X, W)), ∃! a : Γ(P₀.A.left, m ⁻¹ᵁ W),
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
    intro W f
    refine existsUnique_section_of_locally_regular P₀ u Hm χ hu (m ⁻¹ᵁ W) (fun z => s z W f) fun z hz => ?_
    have hz' : ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ) ∈ W := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW₀, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hz' W.isOpen
    have hle' : W₀ ≤ W := hle
    obtain ⟨a, ha⟩ := GlobalTheory.T.holomorphic_lift_regular_of_periods_zero hL P₀ u Hm χ hu R x₀ X p m hp hpb D s hD hs W₀ hW₀ W₀ le_rfl (resG X hle' f)
    refine ⟨m ⁻¹ᵁ W₀, a, fun _ hy => hle' hy, (top_le_preimage_iff_mem ((u.ex z).left ≫ m) W₀).2 hzW₀, fun z' hz' => ?_⟩
    exact (ha z' hz').trans ((hs.der z').res W W₀ hle' hz' f)
  choose d hd hu' using key
  have ext : ∀ (W : X.Opens) (f : Γ(X, W)) (a : Γ(P₀.A.left, m ⁻¹ᵁ W)),
      (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f) → d W f = a :=
    fun W f a h => (hu' W f a h).symm
  refine ⟨d, ⟨fun W _ f f' => ext W _ _ fun z hz => ?_, fun W _ f f' => ext W _ _ fun z hz => ?_,
    fun W W' i _ f => ext W' _ _ fun z hz => ?_, fun W _ r => ext W _ _ fun z hz => ?_⟩⟩
  · rw [valAt'_add, hd W f z hz, hd W f' z hz, (hs.der z).add W hz]
  · rw [valAt'_add, valAt'_mul, valAt'_mul, valAt'_comp, valAt'_comp, hd W f z hz, hd W f' z hz,
      (hs.der z).mul W hz]
  · rw [(hs.der z).res W W' i hz, ← hd W f z fun _ hy => i (hz hy)]
    exact valAt'_res _ _ _ hz
  · have e : constFn p W r = resG X le_top (constFn p ⊤ r) := by
      unfold constFn
      exact (congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
        (Scheme.Hom.appLE_map p (U := ⊤) (V := ⊤) (V' := W) le_top (homOfLE le_top).op)).symm
    rw [e, (hs.der z).res ⊤ W le_top hz, hs.base]
    exact valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz

end GlobalTheory
end

