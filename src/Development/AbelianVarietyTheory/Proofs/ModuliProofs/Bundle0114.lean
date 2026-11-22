import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TateIsoFieldExt

theorem exists_unit_of_pow_eq_one {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] [CharZero K]
    (i : K →+* Ω) (n : ℕ) (hn : 0 < n) (z : Ωˣ) (hz : z ^ n = 1) :
    ∃ u : Kˣ, Units.map i.toMonoidHom u = z := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have h2 : IsPrimitiveRoot (i ξ) n := hξ.map_of_injective i.injective
  have hz' : (z : Ω) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  obtain ⟨j, -, hj⟩ := h2.eq_pow_of_pow_eq_one hz'
  refine ⟨(hξ.isUnit hn.ne').unit ^ j, Units.ext ?_⟩
  simpa using hj

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
  {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) {Q Q' : Type} [Group Q] [Group Q'] (f : Q →* Q')
  {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
  {e : ℕ → Q → Q → Kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}

theorem units_map_injective : Function.Injective (Units.map i.toMonoidHom) :=
  Units.map_injective i.injective

theorem up (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y))
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I : TateIso D K Q act e) :
    ∃ I' : TateIso D Ω Q' act' e', ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  refine ⟨{ ζ := fun n => Units.map i.toMonoidHom (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (units_map_injective i)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n v => f (I.ev n v)
            add := fun n a b => by rw [I.add, map_mul]
            lin := fun n c a => by rw [I.lin, hact]
            ker := fun n hn a => by rw [← I.ker n hn a, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm]
            isom := fun n hn a b => by rw [← map_zpow, he]; exact I.isom n hn a b },
    fun n _ => ⟨rfl, fun _ => rfl⟩⟩
  · obtain ⟨y, hy, rfl⟩ := honto n hn z hz
    obtain ⟨a, rfl⟩ := (I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]

theorem down [IsAlgClosed K] [CharZero K] (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y)) (hone : ∀ c, act c 1 = 1)
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I' : TateIso D Ω Q' act' e') :
    ∃ I : TateIso D K Q act e, ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  have h1 : ∀ n, ∃ u : Kˣ, 0 < n → Units.map i.toMonoidHom u = I'.ζ n := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one i n hn _ (I'.ζ_prim n hn).pow_eq_one
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hn⟩
  have h2 : ∀ n v, ∃ y : Q, (0 < n → f y = I'.ev n v) ∧ (¬ 0 < n → y = 1) := fun n v => by
    by_cases hn : 0 < n
    · obtain ⟨y, -, hy⟩ := honto n hn _ ((I'.onto n hn _).2 ⟨v, rfl⟩)
      exact ⟨y, fun _ => hy, fun h => absurd hn h⟩
    · exact ⟨1, fun h => absurd h hn, fun _ => rfl⟩
  choose ζ hζ using h1
  choose ev hev hev0 using h2
  refine ⟨{ ζ := ζ
            ζ_prim := fun n hn => ?_
            ζ_pow := fun n m hn hm => units_map_injective i ?_
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => by rw [← I'.ker n hn a, ← hev n a hn, map_eq_one_iff f hinj]
            onto := fun n hn z => ?_
            tower := fun n m hn hm a => hinj ?_
            isom := fun n hn a b => ?_ },
    fun n hn => ⟨by rw [← hζ n hn]; rfl, fun v => (hev n v hn).symm⟩⟩
  · refine IsPrimitiveRoot.of_map_of_injective ?_ (units_map_injective i)
    rw [hζ n hn]; exact I'.ζ_prim n hn
  · rw [map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, I'.ζ_pow n m hn hm]
  · by_cases hn : 0 < n
    · apply hinj
      rw [map_mul, hev _ _ hn, hev _ _ hn, hev _ _ hn, I'.add]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hev0 _ _ hn, _root_.mul_one]
  · by_cases hn : 0 < n
    · apply hinj
      rw [hact, hev _ _ hn, hev _ _ hn, I'.lin]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hone]
  · rw [← map_eq_one_iff f hinj, map_pow, I'.onto n hn]
    refine exists_congr fun a => ?_
    rw [← hev n a hn, hinj.eq_iff]
  · rw [map_pow, hev _ _ (Nat.mul_pos hn hm), hev _ _ hn, I'.tower n m hn hm]
  · rw [← he, map_zpow, hζ n hn, hev _ _ hn, hev _ _ hn]
    exact I'.isom n hn a b

end Abstract

noncomputable def precomp {S : Scheme.{0}} {T T' : Over S} (g : T' ⟶ T) (A : Over S) [GrpObj A] :
    (T ⟶ A) →* (T' ⟶ A) where
  toFun y := g ≫ y
  map_one' := MonObj.comp_one g
  map_mul' a b := MonObj.comp_mul g a b

theorem tateIso_fieldExt : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S), (∀ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v) ∧ ∀ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), (∀ c, IsMonHom (act c)) → ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v := by
  intro hL E _ _ _ H D S P act K Ω _ _ _ _ _ i x
  obtain ⟨hinj, honto⟩ := GlobalTheory.T.torsion_points_descend_field_extension hL S P K Ω i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have honto' : ∀ n, 0 < n → ∀ z : Over.mk (spMap i ≫ x) ⟶ P.A, z ^ n = 1 →
      ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ precomp g P.A y = z :=
    fun n hn z hz => honto n z (Nat.cast_ne_zero.mpr hn.ne') hz
  refine ⟨fun I => up D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun n y y' c => GlobalTheory.T.weilPairing_fieldExtension_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I,
    fun I' hm => down D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun c => ?_) (fun n y y' c => GlobalTheory.T.weilPairing_fieldExtension_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I'⟩
  haveI := hm c
  exact MonObj.one_comp (act c)

end GlobalTheory.TateIsoFieldExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsValuesLineFibre
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open scoped Matrix Topology

namespace GlobalTheory.ThetaFamily

theorem exists_values_line (hT : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) :
    ∃ v : P.L.ι → (Sp ℂ ⟶ P.A.left) → ℂ, ∀ s : P.L.Sec, ∃ a : ℂ, ∀ i (x : Sp ℂ ⟶ P.A.left), x ≫ P.A.hom = 𝟙 _ →
      ⊤ ≤ x ⁻¹ᵁ P.L.U i → valAt' x (P.L.U i) (s.f i) = a * v i x := by
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hT ℂ P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  refine ⟨fun i x => valAt' x _ ((β i₀).f (fun _ => i)), fun s => ?_⟩
  obtain ⟨a, ha, -⟩ := hβ (secToPow s 1)
  refine ⟨a i₀, fun i x hx hi => ?_⟩
  have hi' : ⊤ ≤ x ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
  have e := (congrArg (valAt' x _) ((ha (fun _ => i)).trans (su _))).trans ((valAt'_mul x _ _ _).trans
    (congrArg (· * _) (valAt'_constFn x _ hx _ _ hi')))
  refine Eq.trans ?_ e
  exact ((valAt'_res x _ (s.f i ^ 1) hi').trans (by rw [pow_one])).symm

theorem exists_values_line_fibre (hT : Out.GlobalSectionsRankAlgClosed) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (z : Sp ℂ ⟶ S) :
    ∃ v : (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).ι → (Sp ℂ ⟶ pullback o.t.G.hom z) → ℂ,
      ∀ s : (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).Sec, ∃ a : ℂ, ∀ i (x : Sp ℂ ⟶ pullback o.t.G.hom z),
        x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).U i →
        valAt' x ((o.t.PP.L.pull (pullback.fst o.t.G.hom z)).U i) (s.f i) = a * v i x := by
  have h := isGrpPullback_pullback o.t.G z
  obtain ⟨hL, hr, ⟨c', w, g, -⟩, hs⟩ := Out.CubePf.cubePull S _ o.t.G _ (cubeMapOf h) o.t.PP o.t.cub
  have semi := IsSemiAbelian.pullback z o.t.G o.t.semi
  have := semi.smooth
  obtain ⟨am, kt⟩ := amplePt _ _ z _ _ _ h _ _ o.t.PP.isLB hL ⟨w, g⟩ o.ample o.ktriv
  have := semi.geomConnected
  have : ConnectedSpace ((Over.pullback z).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := ((Over.pullback z).obj o.t.G).hom) (𝟙 _) (𝟙 _)
      ((Over.pullback z).obj o.t.G).hom
      (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected ((Over.pullback z).obj o.t.G).hom
    (eSec ((Over.pullback z).obj o.t.G) (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := hs o.t.sym
  exact exists_values_line hT
    { A := (Over.pullback z).obj o.t.G, g := d, smoothDim := hd, L := o.t.PP.L.pull (pullback.fst o.t.G.hom z),
      isLB := hL, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) h.1 o.proper, ‹_›⟩
      rigid := ⟨_, hr⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }

theorem exists_ratio_fibre (hT : Out.GlobalSectionsRankAlgClosed) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (u : Sp ℂ ⟶ S) (V : S.Opens) (θ₀ : ∀ j, Γ(o.t.G.left, o.t.G.hom ⁻¹ᵁ V ⊓ o.t.PP.L.U j))
    (hθ₀ : θ₀ ∈ secOn o.t.PP.L (o.t.G.hom ⁻¹ᵁ V))
    (nz : ∀ y ∈ V, ∃ (x : o.t.G.left) (j : o.t.PP.L.ι), o.t.G.hom x = y ∧ x ∈ o.t.G.left.basicOpen (θ₀ j))
    (hu : ⊤ ≤ u ⁻¹ᵁ V) (σ : LB.Sec (o.t.PP.L.pull (pullback.fst o.t.G.hom u))) :
    ∃ a : ℂ, ∀ j (x : Sp ℂ ⟶ pullback o.t.G.hom u),
      x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ o.t.PP.L.U j →
      valAt' x ((o.t.PP.L.pull (pullback.fst o.t.G.hom u)).U (fun _ => j)) (σ.f (fun _ => j)) =
        a * valAt' (x ≫ pullback.fst _ _) (o.t.G.hom ⁻¹ᵁ V ⊓ o.t.PP.L.U j) (θ₀ j) := by
  have := o.t.semi.smooth
  have mem : ∀ x, pullback.fst o.t.G.hom u x ∈ o.t.G.hom ⁻¹ᵁ V := fun x =>
    (congrArg (fun q => q x ∈ V) (pullback.condition (f := o.t.G.hom) (g := u))).mpr (hu (Set.mem_univ _))
  obtain ⟨t, ht⟩ := HolSec.exists_sec_pull o.t.PP.L _ _ mem θ₀ hθ₀
  obtain ⟨v, hv⟩ := exists_values_line_fibre hT o u
  obtain ⟨g₀, j₀, hg₀, hb₀⟩ := nz _ (hu (Set.mem_univ (default : PrimeSpectrum ℂ)))
  obtain ⟨g, hg₁, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback o.t.G.hom u) g₀ _ hg₀
  obtain ⟨x₀, hx₀, hx₁⟩ := ComplexPoints.exists_point_mem (pullback.snd o.t.G.hom u)
    (Z := (pullback.fst o.t.G.hom u ⁻¹ᵁ o.t.G.left.basicOpen (θ₀ j₀) : Scheme.Opens _))
    (TopologicalSpace.Opens.isOpen _).isLocallyClosed ⟨g, by
      show pullback.fst o.t.G.hom u g ∈ o.t.G.left.basicOpen (θ₀ j₀)
      rw [hg₁]; exact hb₀⟩
  have hx₂ : ⊤ ≤ (x₀ ≫ pullback.fst o.t.G.hom u) ⁻¹ᵁ o.t.G.left.basicOpen (θ₀ j₀) := fun p _ => hx₁ p
  obtain ⟨c, hc⟩ := hv t
  obtain ⟨a, ha⟩ := hv σ
  have m : ∀ j (x : Sp ℂ ⟶ pullback o.t.G.hom u), ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ o.t.PP.L.U j →
      ⊤ ≤ x ⁻¹ᵁ (o.t.PP.L.pull (pullback.fst o.t.G.hom u)).U (fun _ => j) := fun j x h p hp => mem_pull.2 (h hp)
  have hj₀ : ⊤ ≤ (x₀ ≫ pullback.fst o.t.G.hom u) ⁻¹ᵁ o.t.PP.L.U j₀ :=
    top_le_preimage_mono _ ((o.t.G.left.basicOpen_le _).trans inf_le_right) hx₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine (top_le_preimage_basicOpen_iff _ _ _).1 hx₂ ?_
    rw [← ht j₀ x₀ hj₀, hc _ x₀ hx₀ (m _ _ hj₀), zero_mul]
  refine ⟨a / c, fun j x h₁ h₂ => ?_⟩
  rw [← ht j x h₂, hc _ x h₁ (m _ _ h₂), ha _ x h₁ (m _ _ h₂)]
  field_simp

theorem exists_sec_const_mul {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp ℂ) (s : L.Sec) (a : ℂ) :
    ∃ t : L.Sec, ∀ i (x : Sp ℂ ⟶ X), x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ L.U i →
      valAt' x (L.U i) (t.f i) = a * valAt' x (L.U i) (s.f i) := by
  refine ⟨⟨fun i => constFn p _ a * s.f i, fun i j => ?_⟩, fun i x hx hi =>
    (valAt'_mul x _ _ _).trans (congrArg (· * _) (valAt'_constFn x _ hx _ _ hi))⟩
  rw [map_mul, map_mul, s.compat i j, mul_left_comm]
  congr 2
  have r : ∀ (U W : X.Opens) (h : W ≤ U), (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p W a :=
    fun U W h => (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
      (Scheme.Hom.appLE_map p (U := ⊤) (V := U) le_top (homOfLE h).op) :)
  rw [r, r]

theorem thetaChar_ne_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ) :
    thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ≠ 0 := by
  have hs : ((2 : ℂ)⁻¹ • (τ + τᵀ)).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hi : ((2 : ℂ)⁻¹ • (τ + τᵀ)).map Complex.im = τ.map Complex.im := by
    ext i j
    have := congrFun (congrFun hp.1 i) j
    simp at this
    simp [this]
    ring
  have h := CanTh.thetaChar_ne_zero hs (hi ▸ hp) a b
  have e : ∀ v : Fin g → ℂ, v ⬝ᵥ ((2 : ℂ)⁻¹ • (τ + τᵀ)) *ᵥ v = v ⬝ᵥ τ *ᵥ v := fun v => by
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, Matrix.mulVec_transpose,
      dotProduct_comm v (v ᵥ* τ), ← Matrix.dotProduct_mulVec, smul_eq_mul]
    ring
  unfold thetaChar at h ⊢
  simpa only [e] using h

end GlobalTheory.ThetaFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixGeometricTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

theorem fix_geometric_torsion {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S : Scheme.{0}}
    {s : S ⟶ Sp o} (t : TObj g k J b s) (θ : t.A ⟶ t.A) [IsMonHom θ] (hpt : ∀ i, t.pt i ≫ θ = t.pt i)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ t.A) (hy : y ^ k = 1) : y ≫ θ = y := by
  obtain ⟨c, rfl, -⟩ := t.bij K x y hy
  let F : (Over.mk x ⟶ t.A) →* (Over.mk x ⟶ t.A) := IsMonHom.monoidHom θ (Over.mk x)
  refine (map_list_prod F _).trans (congrArg List.prod ?_)
  rw [List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => (map_pow F _ _).trans (congrArg (· ^ (c i).val) ?_))
  show (_ ≫ t.pt i) ≫ θ = _
  rw [Category.assoc, hpt]

theorem tObj_rigid : Out.Laws → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (f : S ⟶ S'), 3 ≤ k → ∀ φ φ' : t.A.left ⟶ t'.A.left, IsGrpPullback t.A t'.A f φ → IsGrpPullback t.A t'.A f φ' → LBIso t.L (t'.L.pull φ) → LBIso t.L (t'.L.pull φ') → (∀ i, (t.pt i).left ≫ φ = (t.pt i).left ≫ φ') → φ = φ' := by
  intro hL o _ g k J b S S' s s' t t' f hk φ φ' hφ hφ' hl hl' hpt
  obtain ⟨θ, hθ, e⟩ := grpPullback_iso hφ hφ'
  have hη : ∀ i, t.pt i ≫ θ.hom = t.pt i := fun i => by
    apply Over.OverMorphism.ext
    apply hφ'.1.hom_ext
    · rw [Over.comp_left, Category.assoc, e]
      exact hpt i
    · rw [Over.w, Over.w]
  have h₁ : LBIso (t.L.pull θ.hom.left) (t'.L.pull φ) :=
    LBIso.chartPull (chartPullPull t.L _ θ.hom.left rfl) (chartPullSame t'.L _ _ _ θ.hom.left fun _ => e.symm) hl'
  obtain ⟨w, hw⟩ : LBIso t.L (t.L.pull θ.hom.left) :=
    LBIso.trans t.isLB (pull_isLB t'.isLB φ) (pull_isLB t.isLB _) hl h₁.symm
  have hku : IsUnit (k : Γ(S, ⊤)) := by
    simpa using b.unit.map ((Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ s.appTop).hom
  have := t.ab.comm
  have := t.ab.smooth
  have : Etale (Out.mulA t.A k).left := GrpTangent.etale_id_pow t.A hku
  have h : θ.hom = 𝟙 _ := by
    refine serre_any_base hL t.pol k hk θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric t.A k θ.hom (fix_geometric_torsion t θ.hom hη))
    obtain ⟨u, hu⟩ := gen_of_iso ((isGen_iff w).1 hw) (t.A.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut t.L _ _ _ _ fun n => ?_) u hu
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  rw [← e, h, Over.id_left, Category.id_comp]

end GlobalTheory.TUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ThetaToObj

section Comb
variable {Q L : Type} [AddCommGroup L] {n : ℕ}

theorem add_zero' [Group Q] {f : L → Q} (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 1 := by
  have := hf 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem add_nsmul' [Group Q] {f : L → Q} (hf : ∀ x y, f (x + y) = f x * f y) (m : ℕ) (x : L) :
    f (m • x) = f x ^ m := by
  induction m with
  | zero => rw [zero_smul, pow_zero, add_zero' hf]
  | succ m ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem ext_basis [CommGroup Q] (bas : (Fin n → ℤ) ≃ₗ[ℤ] L) {f f' : L → Q} (hf : ∀ x y, f (x + y) = f x * f y)
    (hf' : ∀ x y, f' (x + y) = f' x * f' y) (h : ∀ i, f (bas (Pi.single i 1)) = f' (bas (Pi.single i 1))) (x : L) :
    f x = f' x := by
  let F : L →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) fun x y => by rw [hf]; rfl
  let F' : L →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (f' x)) fun x y => by rw [hf']; rfl
  have : F.toIntLinearMap ∘ₗ bas.toLinearMap = F'.toIntLinearMap ∘ₗ bas.toLinearMap := by
    refine (Pi.basisFun ℤ (Fin n)).ext fun i => ?_
    rw [Pi.basisFun_apply]
    exact congrArg Additive.ofMul (h i)
  have e := LinearMap.congr_fun this (bas.symm x)
  simpa [F, F'] using e

theorem exists_comb [CommGroup Q] (bas : (Fin n → ℤ) ≃ₗ[ℤ] L) (p : Fin n → Q) (k : ℕ) (hp : ∀ i, p i ^ k = 1) :
    ∃ f : L → Q, (∀ x y, f (x + y) = f x * f y) ∧ (∀ x, f (k • x) = 1) ∧ ∀ i, f (bas (Pi.single i 1)) = p i := by
  have hf : ∀ x y : L, ∏ i, p i ^ bas.symm (x + y) i = (∏ i, p i ^ bas.symm x i) * ∏ i, p i ^ bas.symm y i := by
    intro x y
    simp only [map_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  refine ⟨fun x => ∏ i, p i ^ bas.symm x i, hf, fun x => ?_, fun i => ?_⟩
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, hp, one_zpow]
  · beta_reduce
    rw [LinearEquiv.symm_apply_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp

end Comb

theorem smul_mem_of_mul {O L : Type} [CommRing O] [AddCommGroup L] [Module O L] {I J : Ideal O} {M : ℕ}
    (h : I * J = Ideal.span {(M : O)}) {u : O} (hu : u ∈ I) {x : L} (hx : x ∈ J • (⊤ : Submodule O L)) :
    ∃ y : L, u • x = M • y := by
  have h1 : u • x ∈ (I * J) • (⊤ : Submodule O L) := by
    rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hu hx
  rw [h, Submodule.ideal_span_singleton_smul] at h1
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
  exact ⟨y, by rw [← hy, Nat.cast_smul_eq_nsmul]⟩

theorem isGrpPullback_of_iso {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (φ : G' ≅ G) [IsMonHom φ.hom] :
    IsGrpPullback G' G (𝟙 S) φ.hom.left := by
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget S).map φ.hom))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x ≫ φ.hom := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y ≫ φ.hom := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [j]

theorem exists_obj_under : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (o : Type) [CommRing o] [Algebra o (KA l)] (b : TBase o l.A) (ρ : o) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (t : TObj g l.A J b (s ≫ spMap (algebraMap o (KA l)))) (τ : SAB H S), l.M ∣ l.A → IsSympBasis D bas → IsFractionRing o (KA l) → algebraMap o (KA l) ρ = (baseKA l).ρ → algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ → (IsReduced S ∨ IsLocallyNoetherian S) → IsPEL D a bas ρ t τ → ∃ ob : Obj D l (baseKA l) s, ObjUnder ob a bas t := by
  intro _ _ E _ _ _ H D g J a bas l o _ _ b ρ S s t τ hMA _ _ hρ hζ _ hP
  obtain ⟨φ, hmon, hL, hact, hgeo⟩ := hP
  obtain ⟨r, hr⟩ := hMA
  have hrpos : 0 < r := Nat.pos_of_ne_zero fun h => by
    have := l.A_pos
    rw [hr, h] at this
    simp at this
  have hMpos : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨hab, hamp, hk⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S t.A τ.G (𝟙 S)
    φ.hom.left t.L τ.PP.L t.isLB τ.PP.isLB t.ab (isGrpPullback_of_iso φ) hL
  let j : 𝟙_ (Over S) ⟶ Out.baseOver S := Over.homMk (𝟙 S) (by simp)
  obtain ⟨f, fadd, fker, fbas⟩ := exists_comb (Q := 𝟙_ (Over S) ⟶ τ.G) bas (fun i => j ≫ t.pt i ≫ φ.inv) l.A
    fun i => by
      rw [← MonObj.comp_pow, ← MonObj.pow_comp, t.torsion, MonObj.one_comp, MonObj.comp_one]
  obtain ⟨e', he', e, he, hee⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)
  refine ⟨⟨τ, hab.proper, hamp t.ample, hk t.ktriv, fun x => f (r • e • x), fun x y => ?_, fun x hx => ?_, f, fadd, fker,
    fun K _ _ x β hβ => ?_⟩, φ, hmon, hL, hact, fun i => ?_⟩
  · rw [smul_add, smul_add, fadd]
  · obtain ⟨y, hy⟩ := smul_mem_of_mul ((mul_comm _ _).trans l.prod) he hx
    rw [hy, smul_smul, mul_comm, ← hr, fker]
  · have : CharZero K := RingHom.charZero_iff β.injective |>.1 inferInstance
    obtain ⟨hd, I, hI, hev⟩ := hgeo K x (β.comp (algebraMap o (KA l))) (by
      rw [← Category.assoc, hβ, ← Spec.map_comp]; rfl)
    have hA : ∀ y, toUnit (Over.mk x) ≫ f y = I.ev l.A y := by
      refine ext_basis (Q := Over.mk x ⟶ τ.G) bas (fun y z => ?_) (I.add _) fun i => ?_
      · rw [fadd, MonObj.comp_mul]
      · rw [fbas, ← cancel_mono φ.hom, hev]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [← Category.assoc]
        congr 1
    refine ⟨by rw [← hρ]; exact hd, I, by rw [← hζ]; exact hI, hA, fun y hy => ?_⟩
    obtain ⟨z, hz⟩ := smul_mem_of_mul l.prod he' hy
    have h1 : y = e • y + l.M • z := by rw [← hz, ← add_smul, add_comm, hee, one_smul]
    rw [hA, add_nsmul' (I.add _), hr, I.tower _ _ hMpos hrpos]
    conv_rhs => rw [h1, I.add, (I.ker _ hMpos _).2 ⟨z, rfl⟩, _root_.mul_one]
  · show (f _ ≫ φ.hom).left = _
    rw [fbas]
    simp [j]

end GlobalTheory.ThetaToObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

namespace GlobalTheory.AmpleBaseChange

theorem relAmple_of_isPullback {S S' : Scheme.{0}} {B : Over S} [IsProper B.hom] {M : LB B.left}
    (hM : M.IsLB) (hA : Out.RelAmple B M) {t : S' ⟶ S} {X : Scheme.{0}} {π : X ⟶ B.left}
    {f : X ⟶ S'} (h : IsPullback π f B.hom t) : Out.RelAmple (Over.mk f) (M.pull π) := by
  have hp : IsProper (Over.mk f).hom := MorphismProperty.of_isPullback (P := @IsProper) h ‹_›
  refine AmpleLocal.relAmple_of_locally S' (Over.mk f) (M.pull π) (pull_isLB hM π)
    inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := t s) trivial
  exact ⟨t ⁻¹ᵁ V, hs, PolBaseChange.relAmple_restrict (A' := Over.mk f) h hM hA V hV⟩

theorem isProjBy_smooth_isProper_geometricallyIntegral :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom t → IsProjBy f ∧ Smooth f ∧ IsProper f ∧ GeometricallyIntegral f := by
  intro S B _ M hB hM hA R _ t X π f h
  have := hB.proper
  have hs : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) h hB.smooth
  refine ⟨?_, hs, MorphismProperty.of_isPullback (P := @IsProper) h hB.proper,
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ f hs
      (MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hB.geomConnected)⟩
  obtain ⟨N, -, m, s, hN, hv⟩ := veryAmpleBy_of_relAmple (A := Over.mk f) (pull_isLB hM π)
    (relAmple_of_isPullback hM hA h) (𝟙 X) (Category.id_comp f) (pull_isLB hM π)
    (LBIso.chartPull (chartPullId _) (chartPullPull (M.pull π) (𝟙 X) (𝟙 X) rfl)
      (PolBaseChange.lbIso_refl (pull_isLB hM π)))
  exact ⟨_, hN, m, s, hv⟩

end GlobalTheory.AmpleBaseChange
end
end

