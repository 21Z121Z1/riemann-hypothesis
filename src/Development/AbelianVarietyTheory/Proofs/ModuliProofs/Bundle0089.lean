import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImportsBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnitBallVal

theorem dvd_of_norm_le {C O : Type} [NormedField C] [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C))
    (hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x) {a b : O}
    (h : ‖algebraMap O C b‖ ≤ ‖algebraMap O C a‖) : a ∣ b := by
  by_cases ha : algebraMap O C a = 0
  · have hb : algebraMap O C b = 0 := by
      rw [ha, norm_zero] at h
      exact norm_le_zero_iff.mp h
    have hb0 : b = 0 := hinj (by rw [hb, map_zero])
    rw [hb0]
    exact dvd_zero a
  · obtain ⟨y, hy⟩ := hsurj (algebraMap O C b / algebraMap O C a) (by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr ha)).mpr h)
    refine ⟨y, hinj ?_⟩
    rw [map_mul, hy]
    field_simp

theorem main : ∀ (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CommRing O] [Algebra O C], IsUnitBall O C → ∃ (_ : IsDomain O), ValuationRing O ∧ Ring.DimensionLEOne O ∧ IsFractionRing O C := by
  intro C O _ _ _ _ hO
  obtain ⟨hinj, hball⟩ := hO
  have hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x := fun x hx => (hball x).mpr hx
  have hle : ∀ y : O, ‖algebraMap O C y‖ ≤ 1 := fun y => (hball _).mp ⟨y, rfl⟩
  have hdom : IsDomain O := hinj.isDomain (algebraMap O C)

  have hunit : ∀ y : O, ‖algebraMap O C y‖ = 1 → IsUnit y := fun y hy =>
    isUnit_of_dvd_one (dvd_of_norm_le hinj hsurj (by rw [map_one, norm_one, hy]))
  refine ⟨hdom, { cond' := fun a b => ?_ }, ⟨fun {P} hP0 hP => ?_⟩, ?_⟩
  · rcases le_total ‖algebraMap O C b‖ ‖algebraMap O C a‖ with h | h
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inl hc.symm⟩
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inr hc.symm⟩
  ·
    obtain ⟨p, hpP, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    have hp' : algebraMap O C p ≠ 0 := fun h0 => hp0 (hinj (by rw [h0, map_zero]))
    have key : ∀ m : O, m ∉ P → IsUnit m := by
      intro m hm
      apply hunit
      refine le_antisymm (hle m) (not_lt.mp fun hlt => hm ?_)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hp') hlt
      obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj (a := p) (b := m ^ n)
        (by rw [map_pow, norm_pow]; exact hn.le)
      refine hP.mem_of_pow_mem n ?_
      rw [hc]
      exact P.mul_mem_right c hpP
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    have hMP : M ≤ P := fun m hm => by
      by_contra hmP
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M hm (key m hmP))
    rwa [le_antisymm hPM hMP]
  · refine (isLocalization_iff (nonZeroDivisors O) C).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact IsUnit.mk0 _ fun h0 => nonZeroDivisors.ne_zero hy (hinj (by rw [h0, map_zero]))
    · intro z
      by_cases hz : ‖z‖ ≤ 1
      · obtain ⟨y, hy⟩ := hsurj z hz
        exact ⟨⟨y, 1⟩, by simp [hy]⟩
      · rw [not_le] at hz
        have hz0 : z ≠ 0 := by
          rintro rfl
          rw [norm_zero] at hz
          linarith
        obtain ⟨y, hy⟩ := hsurj z⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz.le)
        have hy0 : y ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero (by
          rintro rfl
          rw [map_zero] at hy
          exact inv_ne_zero hz0 hy.symm)
        exact ⟨⟨1, ⟨y, hy0⟩⟩, by simp [hy, hz0]⟩
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩

end GlobalTheory.UnitBallVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelCoverField
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

section

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {G' : Over T.left} [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem exists_secEquiv (h : IsGrpPullback G' G T.hom φ) :
    ∃ Φ : (𝟙_ (Over T.left) ⟶ G') ≃* (T ⟶ G), ∀ σ, (Φ σ).left = σ.left ≫ φ := by
  let j : T ≅ Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) := Over.isoMk (Iso.refl _) (by simp)
  let Ψ : (Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ G) ≃* (T ⟶ G) :=
    MulEquiv.ofBijective (preHom j.hom) ⟨fun x y e => (cancel_epi j.hom).1 e,
      fun y => ⟨j.inv ≫ y, j.hom_inv_id_assoc y⟩⟩
  exact ⟨(ObjPull.pushEquiv h _).trans Ψ, fun σ => Category.id_comp _⟩

end

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
  {l l₂ : Level H} {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {s : S ⟶ Sp B}

theorem sabMap_lbIso {S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem pushEquiv_act {S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (T : Over S')
    (c : 𝓞 E) (g : T ⟶ t'.G) :
    ObjPull.pushEquiv m.cart T (g ≫ t'.act.act c) = ObjPull.pushEquiv m.cart T g ≫ t.act.act c := by
  apply Over.OverMorphism.ext
  show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
  rw [Category.assoc, m.act, Category.assoc]

theorem levStr_of_obj (o : Obj D l b s) (T : Over S) (o' : Obj D l₂ b₂ (T.hom ≫ s)) (m : SABMap o'.t o.t T.hom)
    (hW : ∀ (T' : Over T.left) (k : ℤ) (x y : T' ⟶ o'.t.G) (x₀ y₀ : Over.mk (T'.hom ≫ T.hom) ⟶ o.t.G)
      (c : Γ(T'.left, ⊤)ˣ), x₀.left = x.left ≫ m.φ → y₀.left = y.left ≫ m.φ →
      (Out.WeilIs o'.t.G o'.t.PP.L k x y c ↔ Out.WeilIs o.t.G o.t.PP.L k x₀ y₀ c))
    (h1 : ∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m.φ = T.hom ≫ (o.eta a).left)
    (h2 : ∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = T.hom ≫ (o.etaA a).left) :
    ∃ χ θ : D.La → (T ⟶ o.t.G), LevStr o b₂ T χ θ ∧ (∀ a, (χ a).left = (o'.eta a).left ≫ m.φ) ∧
      ∀ a, (θ a).left = (o'.etaA a).left ≫ m.φ := by
  obtain ⟨Φ, hΦ⟩ := exists_secEquiv m.cart
  refine ⟨fun a => Φ (o'.eta a), fun a => Φ (o'.etaA a), ⟨fun a c => ?_, fun a ha => ?_, fun a c => ?_, fun a => ?_,
    fun a => ?_, fun a => ?_, fun k _ _ x β hx y => ?_⟩, fun a => hΦ _, fun a => hΦ _⟩
  · simp only [o'.eta_add, map_mul]
  · simp only [o'.eta_ker a ha, map_one]
  · simp only [o'.etaA_add, map_mul]
  · simp only [o'.etaA_ker, map_one]
  · apply Over.OverMorphism.ext
    rw [← map_pow, hΦ, h1, Over.comp_left, ObjPull.toUnit_left']
  · apply Over.OverMorphism.ext
    rw [← map_pow, hΦ, h2, Over.comp_left, ObjPull.toUnit_left']
  · obtain ⟨x', rfl, rfl⟩ : ∃ (x' : Sp k ⟶ T.left) (h : x' ≫ T.hom = x), y = Over.homMk x' h :=
      ⟨y.left, Over.w y, rfl⟩
    obtain ⟨-, I, hI, hA, hM⟩ := o'.geom k x' β (by rw [← hx, Category.assoc])
    have key : ∀ σ : 𝟙_ (Over T.left) ⟶ o'.t.G, (Over.homMk x' rfl : Over.mk (x' ≫ T.hom) ⟶ T) ≫ Φ σ =
        ObjPull.pushEquiv m.cart (Over.mk x') (toUnit _ ≫ σ) := fun σ => by
      apply Over.OverMorphism.ext
      rw [ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, hΦ, ObjPull.toUnit_left', Category.assoc]
      rfl
    refine ⟨ObjPull.tateMove (ObjPull.pushEquiv m.cart (Over.mk x')).symm (fun c g => ?_) (fun n g g' c hc => ?_) I,
      hI, fun a => ?_, fun a ha => ?_⟩
    · rw [MulEquiv.symm_apply_eq, pushEquiv_act, MulEquiv.apply_symm_apply]
    · exact (hW (Over.mk x') n _ _ g g' _ (ObjPull.pushEquiv_symm_left m.cart (Over.mk x') g).symm
        (ObjPull.pushEquiv_symm_left m.cart (Over.mk x') g').symm).1 hc
    · exact (key _).trans (congrArg _ (hA a))
    · exact (key _).trans (congrArg _ (hM a ha))

theorem obj_of_levStr (o : Obj D l b s) (hρ : b.ρ = b₂.ρ) (T : Over S) (t' : SAB H T.left) (m : SABMap t' o.t T.hom)
    (hW : ∀ (T' : Over T.left) (k : ℤ) (x y : T' ⟶ t'.G) (x₀ y₀ : Over.mk (T'.hom ≫ T.hom) ⟶ o.t.G)
      (c : Γ(T'.left, ⊤)ˣ), x₀.left = x.left ≫ m.φ → y₀.left = y.left ≫ m.φ →
      (Out.WeilIs t'.G t'.PP.L k x y c ↔ Out.WeilIs o.t.G o.t.PP.L k x₀ y₀ c))
    (hLie : ∀ (k : Type) [Field k] (x : Sp k ⟶ T.left) (τ : 𝓞 E →+* k) (n : ℕ),
      LieMult t'.act x τ n ↔ LieMult o.t.act (x ≫ T.hom) τ n)
    (hamp : Out.RelAmple t'.G t'.PP.L) (hk : Out.KTriv t'.G t'.PP.L)
    {χ θ : D.La → (T ⟶ o.t.G)} (h : LevStr o b₂ T χ θ) :
    ∃ (o' : Obj D l₂ b₂ (T.hom ≫ s)) (m' : SABMap o'.t o.t T.hom),
      ((∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = T.hom ≫ (o.eta a).left) ∧
        ∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = T.hom ≫ (o.etaA a).left) ∧
      (∀ a, (χ a).left = (o'.eta a).left ≫ m'.φ) ∧ ∀ a, (θ a).left = (o'.etaA a).left ≫ m'.φ := by
  obtain ⟨Φ, hΦ⟩ := exists_secEquiv m.cart
  have hpr := o.proper
  refine ⟨{ t := t'
            proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
            ample := hamp
            ktriv := hk
            eta := fun a => Φ.symm (χ a)
            eta_add := fun a c => by rw [h.add, map_mul]
            eta_ker := fun a ha => by rw [h.ker a ha, map_one]
            etaA := fun a => Φ.symm (θ a)
            etaA_add := fun a c => by rw [h.addA, map_mul]
            etaA_ker := fun a => by rw [h.kerA a, map_one]
            geom := fun k _ _ x β hx => ?_ }, m, ⟨fun a => ?_, fun a => ?_⟩, fun a => ?_, fun a => ?_⟩
  · have hx' : (x ≫ T.hom) ≫ s = spMap β := by rw [← hx, Category.assoc]
    obtain ⟨hdet, -⟩ := o.geom k (x ≫ T.hom) β hx'
    obtain ⟨I, hI, hA, hM⟩ := h.geom k (x ≫ T.hom) β hx' (Over.homMk x rfl)
    rw [hρ] at hdet
    have key : ∀ σ : T ⟶ o.t.G, ObjPull.pushEquiv m.cart (Over.mk x) (toUnit _ ≫ Φ.symm σ) =
        (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ σ := fun σ => by
      apply Over.OverMorphism.ext
      rw [ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, ← hΦ, ObjPull.toUnit_left',
        MulEquiv.apply_symm_apply]
      rfl
    refine ⟨fun τ => ?_, ObjPull.tateMove (ObjPull.pushEquiv m.cart (Over.mk x)) (fun c g => pushEquiv_act m _ c g)
      (fun n g g' c hc => ?_) I, hI, fun a => ?_, fun a ha => ?_⟩
    · rw [hLie, hLie]
      exact hdet τ
    · exact (hW (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
    · exact (MulEquiv.eq_symm_apply _).2 ((key _).trans (hA a))
    · exact (MulEquiv.eq_symm_apply _).2 ((key _).trans (hM a ha))
  · refine (hΦ _).symm.trans ?_
    dsimp only
    rw [map_pow, MulEquiv.apply_symm_apply, h.low, Over.comp_left, ObjPull.toUnit_left']
  · refine (hΦ _).symm.trans ?_
    dsimp only
    rw [map_pow, MulEquiv.apply_symm_apply, h.lowA, Over.comp_left, ObjPull.toUnit_left']
  · exact ((hΦ _).symm.trans (by rw [MulEquiv.apply_symm_apply])).symm
  · exact ((hΦ _).symm.trans (by rw [MulEquiv.apply_symm_apply])).symm

theorem levelCover_field : Out.Laws → (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G
    : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a
    : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act
    c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n
    : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (S S' : Scheme.{0}) (G : Over S) (G'
    : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L'
    : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull
    φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv
    G' L')) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D
    : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n *
    m) - g.ν n ∧ IsCoprime (g.ν n) (n
    : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
    n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (N : ℕ) (f
    : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (∀ a b, (N : ℤ) ∣ D.EF (f a) (f
    b) - ν * D.EF a b) → ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : Type) [Field
    k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
    : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
    n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj
    G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ
    La], IsAbelianScheme G → IsUnit (n : Γ(S, ⊤)) → ∃ (Z : Over S) (et : La → (Z ⟶
    G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a +
    c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧ ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a +
    c) = et' a * et' c) → (∀ a, et' a ^ n = 1) → ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a) → (∀ (S
    : Scheme.{0}) (P : Out.PolAV S) (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left,
    ⊤)ˣ), 0 < n → IsUnit (n : Γ(T.left,
    ⊤)) → x ^ n = 1 → y ^ n = 1 → c ^ n = 1 → ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T'
    : Over S) (h : T' ⟶ T), Out.WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map
    (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (N : ℕ) (ν
    : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 → ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧ (l.A
    : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞
    E) D.La)) ∧ ∀ a, D.ModN l.A (g.f l.A a - a)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField
    E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂
    : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂
    : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m
    : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫
    s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta
    a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA
    a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ := by
  intro _ hLie hAb hPol hSim hLift _ hTors hLoc hMult E _ _ _ H D l l₂ B _ b b₂ S s o hpq hl hρ hζ
  obtain ⟨hab, hsm, hrig, hsym⟩ := hPol E H D l B b S s o
  obtain ⟨hfree, hfin⟩ := datum_free D
  let P : Out.PolAV S := ⟨o.t.G, hab, _, hsm, o.t.PP.L, o.t.PP.isLB, hrig, hsym, o.ample, o.ktriv⟩
  obtain ⟨V, χ, θ, hV1, hV2, hV3, hV, hext, hex⟩ := exists_levStr_rep o l₂ b₂ hl hζ (hSim E H D hpq).1
    (hLift E H D) (hMult E H D)
    (fun n hn => hTors S o.t.G n D.La hab (by
      have := (b.unit n hn).map (fnOn s)
      rwa [map_natCast] at this))
    (fun N hN T x y c hu hx hy hc => hLoc S P N T x y c hN hu hx hy hc)
  obtain ⟨t', ⟨m₀⟩⟩ : ∃ t' : SAB H V.left, Nonempty (SABMap t' o.t V.hom) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull V.hom o.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨-, hamp, hk⟩ := hAb _ _ o.t.G t'.G V.hom m₀.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB hab m₀.cart
    (sabMap_lbIso m₀)
  obtain ⟨o₂, m, hc, e1, e2⟩ := obj_of_levStr o hρ V t' m₀
    (weilIs_grpPullback_of_comm _ _ o.t.G t'.G V.hom m₀.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB m₀.cart (sabMap_lbIso m₀))
    (hLie _ _ _ o.t.G t'.G V.hom m₀.cm.F o.t.act t'.act m₀.cart m₀.act) (hamp o.ample) (hk o.ktriv) hV
  refine ⟨V.left, V.hom, o₂, m, hV1, hV2, hV3, hc, fun T f o' m' ⟨h1, h2⟩ => ?_⟩
  obtain ⟨χ', θ', hT, f1, f2⟩ := levStr_of_obj o (Over.mk f) o' m'
    (weilIs_grpPullback_of_comm _ _ o.t.G o'.t.G f m'.cm.F o.t.PP.L o'.t.PP.L o.t.PP.isLB o'.t.PP.isLB m'.cart (sabMap_lbIso m')) h1 h2
  obtain ⟨h, g1, g2⟩ := hex _ χ' θ' hT
  have huniq : ∀ h' : T ⟶ V.left, (h' ≫ V.hom = f ∧ ∃ u : ObjMap o' o₂ h', u.toSABMap.φ ≫ m.φ = m'.φ) →
      h' = h.left := by
    rintro h' ⟨hf, u, hu⟩
    refine congrArg CommaMorphism.left (hext (Over.mk f) (Over.homMk h' hf) h (fun a => ?_) fun a => ?_)
    · apply Over.OverMorphism.ext
      rw [g1, f1, Over.comp_left, e1, ← hu, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ m.φ) (u.eta a).symm
    · apply Over.OverMorphism.ext
      rw [g2, f2, Over.comp_left, e2, ← hu, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ m.φ) (u.etaA a).symm
  refine ⟨h.left, ⟨Over.w h, ?_⟩, huniq⟩
  obtain ⟨h', rfl, rfl⟩ : ∃ (h' : T ⟶ V.left) (e : h' ≫ V.hom = f), h = Over.homMk h' e := ⟨h.left, Over.w h, rfl⟩
  obtain ⟨u, hu⟩ := sabCancel pullCubCancel E H _ _ _ o.t o₂.t o'.t V.hom h' m m'
  have key : ∀ (σ' : 𝟙_ (Over T) ⟶ o'.t.G) (σ : 𝟙_ (Over V.left) ⟶ o₂.t.G),
      σ'.left ≫ m'.φ = h' ≫ σ.left ≫ m.φ → σ'.left ≫ u.cm.F = h' ≫ σ.left := fun σ' σ e => by
    apply m.cart.1.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (σ'.left ≫ ·) hu.symm).trans
        (e.trans (Category.assoc _ _ _).symm))
    · rw [Category.assoc, u.cart.1.w, ← Category.assoc, Over.w σ', Category.assoc, Over.w σ]
      simp
  refine ⟨⟨u, fun a => key _ _ ?_, fun a => key _ _ ?_⟩, hu.symm⟩
  · rw [← f1, ← e1, ← g1]
    rfl
  · rw [← f2, ← e2, ← g2]
    rfl

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjDescendLowerLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ObjDesc

open GlobalTheory.ObjPull

theorem exists_geomPt_lift {X Y : Scheme.{0}} (π : X ⟶ Y) [LocallyOfFiniteType π] [Surjective π]
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) : ∃ y : Sp k ⟶ X, y ≫ π = x := by

  have hJ := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨p, -⟩ := (pullback.snd π x).surjective (IsLocalRing.closedPoint k)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Set.nonempty_of_mem (Set.mem_univ p))
    isOpen_univ.isLocallyClosed
  have hc' : IsClosed {c} := hc
  have hpt := pointOfClosedPoint_comp (pullback.snd π x) c hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc' ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hpt, Category.id_comp]

section Sections

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem secPull_injective [Epi f] (h : IsGrpPullback G' G f φ) : Function.Injective (secPull h) := by
  intro e₁ e₂ he
  have key : f ≫ e₁.left = f ≫ e₂.left := by
    rw [← secPull_left h e₁, ← secPull_left h e₂, he]
  exact Over.OverMorphism.ext ((cancel_epi f).1 key)

theorem secPull_eq (h : IsGrpPullback G' G f φ) {e : 𝟙_ (Over S) ⟶ G} {e' : 𝟙_ (Over S') ⟶ G'}
    (he : e'.left ≫ φ = f ≫ e.left) : secPull h e = e' := by

  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
  · rw [secPull_left, he]
  · exact (Over.w _).trans (Over.w e').symm

theorem exists_sec [Epi f] (h : IsGrpPullback G' G f φ) (e' : 𝟙_ (Over S') ⟶ G') (g : S ⟶ G.left)
    (hg : f ≫ g = e'.left ≫ φ) : ∃ e : 𝟙_ (Over S) ⟶ G, e'.left ≫ φ = f ≫ e.left := by

  have hsec : g ≫ G.hom = (𝟙_ (Over S)).hom := by
    apply (cancel_epi f).1
    rw [← Category.assoc, hg, Category.assoc, h.1.w, ← Category.assoc, Over.w e']
    simp
  exact ⟨Over.homMk g hsec, hg.symm⟩

end Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'} {X Y : Scheme.{0}}
  {s : Y ⟶ Sp B} {s' : X ⟶ Sp B'} {π : X ⟶ Y}

def descend [Epi π] [LocallyOfFiniteType π] [Surjective π] (j : B →+* B') (hρ : j b.ρ = b'.ρ) (hζ : j b.ζ = b'.ζ)
    (hs : π ≫ s = s' ≫ spMap j) (o : Obj D l b' s') (t : SAB H Y) (m : SABMap o.t t π)
    (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (e eA : D.La → (𝟙_ (Over Y) ⟶ t.G)) (he : ∀ a, secPull m.cart (e a) = o.eta a)
    (heA : ∀ a, secPull m.cart (eA a) = o.etaA a) : Obj D l b s where
  t := t
  proper := hp
  ample := ha
  ktriv := hk
  eta := e
  eta_add a c := secPull_injective m.cart (by rw [map_mul, he, he, he, o.eta_add])
  eta_ker a h := secPull_injective m.cart (by rw [map_one, he, o.eta_ker a h])
  etaA := eA
  etaA_add a c := secPull_injective m.cart (by rw [map_mul, heA, heA, heA, o.etaA_add])
  etaA_ker a := secPull_injective m.cart (by rw [map_one, heA, o.etaA_ker a])
  geom k _ _ x β hx := by
    obtain ⟨y, rfl⟩ := exists_geomPt_lift π k x
    obtain ⟨β', hβ'⟩ : ∃ β' : B' →+* k, y ≫ s' = spMap β' :=
      ⟨(Spec.preimage (y ≫ s')).hom, (Spec.map_preimage _).symm⟩
    obtain rfl : β = β'.comp j := by
      have : spMap β = spMap (β'.comp j) := by
        rw [← hx, Category.assoc, hs, ← Category.assoc, hβ', spMap_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have hL : LBIso o.t.PP.L (t.PP.L.pull m.cm.F) := by
      obtain ⟨w, hw, -⟩ := m.lin
      exact ⟨w, hw⟩
    obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k y β' hβ'
    rw [RingHom.comp_apply, RingHom.comp_apply, hρ, hζ]
    refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk y)).symm (fun c g => ?_) (fun n g g' c hc => ?_) I,
      hI, fun a => ?_, fun a ha => ?_⟩
    · rw [← GlobalTheory.LiePull.lieMult_pull _ Y X t.G o.t.G π m.cm.F t.act o.t.act m.cart m.act k y τ,
        ← GlobalTheory.LiePull.lieMult_pull _ Y X t.G o.t.G π m.cm.F t.act o.t.act m.cart m.act k y τ]
      exact hdet τ
    · obtain ⟨g, rfl⟩ := (pushEquiv m.cart (Over.mk y)).surjective g
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
      apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
      rw [Category.assoc, ← m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm Y X t.G o.t.G π m.cm.F t.PP.L o.t.PP.L t.PP.isLB o.t.PP.isLB m.cart hL
        (Over.mk y) n _ _ g g' _ (pushEquiv_symm_left m.cart (Over.mk y) g).symm
        (pushEquiv_symm_left m.cart (Over.mk y) g').symm).1 hc
    · refine (pushEquiv_secPull m.cart (Over.mk y) _).symm.trans ?_
      rw [heA, hA]
      rfl
    · refine (pushEquiv_secPull m.cart (Over.mk y) _).symm.trans ?_
      rw [he, hM a ha]
      rfl

def lowerBase {l₂ : Level H} (h : l.Dvd l₂) (b₂ : Base l₂ B') : Base l B' where
  unit := b₂.unit
  ρ := b₂.ρ
  ρ_sq := b₂.ρ_sq
  ζ := b₂.ζ ^ (l₂.A / l.A)
  ζ_prim := b₂.ζ_prim.pow l₂.A_pos (Nat.div_mul_cancel h.2.2).symm

end GlobalTheory.ObjDesc

theorem GlobalTheory.obj_descend_lower_level : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B B₂ : Type) [CommRing B] [CommRing B₂] (b : Base l B) (b₂ : Base l₂ B₂) (j : B →+* B₂) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp B) (s₂ : X ⟶ Sp B₂) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ob₂ : Obj D l₂ b₂ s₂) (ν : Ga → (ob₂.t.G.left ⟶ ob₂.t.G.left)) (t' : SAB H Y) (m : SABMap ob₂.t t' π), l.Dvd l₂ → j b.ρ = b₂.ρ → j b.ζ = b₂.ζ ^ (l₂.A / l.A) → π ≫ s = s₂ ≫ spMap j → IsGaloisCover Ga ρ π → (∀ a, ν a ≫ m.φ = m.φ) → (∀ a, Lowers l ob₂ (fun x => ob₂.eta x ^ (l₂.M / l.M)) (fun x => ob₂.etaA x ^ (l₂.A / l.A)) (ρ a) (ν a)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∃ (ob : Obj D l b s) (m' : SABMap ob₂.t ob.t π), (∀ a, (ob₂.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = π ≫ (ob.eta a).left) ∧ ∀ a, (ob₂.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = π ≫ (ob.etaA a).left := by
  intro _ _ E _ _ _ H D l l₂ B B₂ _ _ b b₂ j X Y π s s₂ Ga _ ρ ob₂ ν t' m hdvd hρ hζ hs hG hν hlow hp ha hk

  have : Epi π := ⟨fun g₁ g₂ hg => (hG.existsUnique_desc (π ≫ g₁)
    (fun a => by rw [← Category.assoc, hG.inv])).unique rfl hg.symm⟩
  have : IsFinite π := hG.fin
  have : Surjective π := hG.onto

  let o := GlobalTheory.ObjLower.lower (b := GlobalTheory.ObjDesc.lowerBase hdvd b₂) ob₂ hdvd rfl rfl

  have desc : ∀ u : D.La → (𝟙_ (Over X) ⟶ ob₂.t.G), (∀ c a, ρ c ≫ (u a).left = (u a).left ≫ ν c) →
      ∃ w : D.La → (𝟙_ (Over Y) ⟶ t'.G), ∀ a, (u a).left ≫ m.φ = π ≫ (w a).left := by
    intro u hu
    have hex : ∀ a, ∃ w : 𝟙_ (Over Y) ⟶ t'.G, (u a).left ≫ m.φ = π ≫ w.left := by
      intro a
      obtain ⟨g, hg, -⟩ := hG.existsUnique_desc ((u a).left ≫ m.φ)
        (fun c => by rw [← Category.assoc, hu c a, Category.assoc, hν c])
      exact GlobalTheory.ObjDesc.exists_sec m.cart (u a) g hg
    exact ⟨fun a => (hex a).choose, fun a => (hex a).choose_spec⟩
  obtain ⟨e, he⟩ := desc (fun a => ob₂.eta a ^ (l₂.M / l.M)) (fun c a => ((hlow c).1 a).symm)
  obtain ⟨eA, heA⟩ := desc (fun a => ob₂.etaA a ^ (l₂.A / l.A)) (fun c a => ((hlow c).2 a).symm)
  exact ⟨GlobalTheory.ObjDesc.descend (b' := GlobalTheory.ObjDesc.lowerBase hdvd b₂) j hρ hζ hs o t' m hp ha hk e eA
    (fun a => GlobalTheory.ObjDesc.secPull_eq m.cart (he a)) (fun a => GlobalTheory.ObjDesc.secPull_eq m.cart (heA a)),
    m, he, heA⟩

end
end

