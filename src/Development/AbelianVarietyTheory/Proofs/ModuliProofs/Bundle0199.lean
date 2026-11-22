import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0196
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueMapToThetaFamilyOpenPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.UnivProp

set_option backward.isDefEq.respectTransparency false

variable {o : Type} [CommRing o] {g n N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}

theorem span_eq_top_of_coset {R : Type} [CommRing R] {v : Ix g (N' ^ 2) → R}
    (h : ∀ q : Ideal R, q.IsPrime → Coset n N' v q) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨c, hc⟩ := h m hm.isPrime 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

theorem pt_eq_of_secCoord {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)} (Y : MMPre n N' I) {R : Type} [CommRing R]
    {x x' : Sp R ⟶ Y.MM} {v : Ix g (N' ^ 2) → R} (e : x ≫ Y.s = x' ≫ Y.s) (h : SecCoord Y.de Y.th x v)
    (h' : SecCoord Y.de Y.th x' v) : x = x' := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Y.s)
  exact (Y.pts R β v (Y.loc R β x v hβ h)).unique ⟨hβ, h⟩ ⟨e.symm.trans hβ, h'⟩

theorem exists_thetaMap (hL : Out.Laws) (hL2 : Out.Laws2) (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N') {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} (Y : MMPre n N' (thIdeal em C)) {S : Scheme.{0}} {s : S ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) (hS : IsReduced S) (hD : Dense (fromSet em C t)) :
    ∃ f : S ⟶ Y.MM, f ≫ Y.s = s ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ S),
      ∃ v, t.HasTh y v ∧ SecCoord Y.de Y.th (y ≫ f) v := by
  classical
  have hloc := fun p : S => GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g N' J b S s t ho p
  choose R hR x v hx hp hth using hloc
  have hβ' : ∀ p, ∃ β : o →+* R p, x p ≫ s = spMap β := fun p => exists_spMap (x p ≫ s)
  choose β hβ using hβ'
  have hin : ∀ p, InMM n N' (thIdeal em C) (β p) (v p) := fun p =>
    GlobalTheory.T.thetaConstants_satisfy_closure_equations_of_dense_class hL hL2 o g n N' J b em C S s t (R p) (β p) (x p) (v p) hn hd ho hS hD (hx p) (hβ p) (hth p)
  have hpt : ∀ p, ∃ y : Sp (R p) ⟶ Y.MM, y ≫ Y.s = spMap (β p) ∧ SecCoord Y.de Y.th y (v p) :=
    fun p => (Y.pts (R p) (β p) (v p) (hin p)).exists
  choose f hf using hpt
  obtain ⟨F, hF⟩ := exists_glue (fun p => Sp (R p)) x hx (fun p => ⟨p, hp p⟩) f (by
    intro i j T _ z z' hz
    obtain ⟨φ, rfl⟩ := exists_spMap z
    obtain ⟨φ', rfl⟩ := exists_spMap z'
    have h1 := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t (R i) T φ (x i) (v i) (hth i)
    have h2 := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t (R j) T φ' (x j) (v j) (hth j)
    rw [hz] at h1
    have hsp : Ideal.span (Set.range fun a => φ (v i a)) = ⊤ :=
      span_eq_top_of_coset (n := n) fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n T _ _ q hn hd h1 hq
    obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b S s t T _ _ _ h1 h2 hsp
    have c1 : SecCoord Y.de Y.th (spMap φ ≫ f i) fun a => φ' (v j a) := by
      have e : (fun a => φ' (v j a)) = fun a => (u : T) * φ (v i a) := funext fun a => hu a
      rw [e]
      exact GlobalTheory.ZM.Coord.scale (GlobalTheory.ZM.Coord.baseChange (hf i).2 φ) u
    have c2 := GlobalTheory.ZM.Coord.baseChange (hf j).2 φ'
    refine pt_eq_of_secCoord Y ?_ c1 c2
    have e := congrArg (· ≫ s) hz
    simp only [Category.assoc, hβ] at e
    simp only [Category.assoc, (hf i).1, (hf j).1]
    exact e)
  refine ⟨F, ?_, ?_⟩
  · refine hom_ext_affine _ _ fun p => ⟨Sp (R p), x p, hx p, hp p, ?_⟩
    rw [← Category.assoc, hF p, (hf p).1, hβ p]
  · intro K _ y
    obtain ⟨p, hyp⟩ : ∃ p, p ∈ Set.range y := ⟨_, IsLocalRing.closedPoint K, rfl⟩
    have := hx p
    obtain ⟨z, hz⟩ := exists_lift_field (x p) y hyp (hp p)
    obtain ⟨φ, rfl⟩ := exists_spMap z
    subst hz
    refine ⟨fun a => φ (v p a), ?_, ?_⟩
    · exact GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t (R p) K φ (x p) (v p) (hth p)
    · rw [Category.assoc, hF]
      exact GlobalTheory.ZM.Coord.baseChange (hf p).2 φ

private theorem exists_tObj_transport_of_eq {o₁ : Type} [CommRing o₁] {g₁ k₁ : ℕ} {J₁ : Type} {b₁ : TBase o₁ k₁}
    {S₁ : Scheme.{0}} {s₁ s₂ : S₁ ⟶ Sp o₁} (h : s₁ = s₂) (u : TObj g₁ k₁ J₁ b₁ s₁) :
    ∃ u' : TObj g₁ k₁ J₁ b₁ s₂, ∀ P : ∀ s : S₁ ⟶ Sp o₁, TObj g₁ k₁ J₁ b₁ s → Prop, P s₁ u → P s₂ u' := by
  subst h
  exact ⟨u, fun _ hP => hP⟩

theorem existsUnique_map_of_wFam : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (F : WFam n em C Mat κ) (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → t.FibShape Mat κ → ∃! f : S ⟶ F.U.toScheme, f ≫ F.U.ι ≫ F.Y.s = s' ∧ TMap t F.univ f := by
  intro hL hL2 g J _ Mat κ n w w' hnp hno
  refine ⟨2, fun j hj o _ b em C d _ _ F S s' t hS hD hFib => ?_⟩
  have hn : 2 ≤ n := hnp.two_le
  have hd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hd2 : n ^ 2 ∣ n ^ j := pow_dvd_pow n hj
  have ho : Odd (n ^ j) := hno.pow
  obtain ⟨f0, hf0s, hf0⟩ := exists_thetaMap hL hL2 hn hd ho F.Y t hS hD
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) (u : TObj g ((n ^ j) ^ 2) J b (y ≫ s')),
      TMap u t y → ∃ x' : Sp K ⟶ F.U.toScheme, x' ≫ F.U.ι = y ≫ f0 ∧ TMap u F.univ x' := by
    intro K _ _ y u hu
    obtain ⟨v, hvt, hvs⟩ := hf0 K y
    have hsh := hFib K y u hu
    have hth : u.HasTh (𝟙 _) v :=
      (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b S s' t (Sp K) (y ≫ s') u y K (𝟙 _) v hu).2 (by simpa using hvt)
    obtain ⟨u', hu'⟩ := exists_tObj_transport_of_eq (show y ≫ s' = (y ≫ f0) ≫ F.Y.s by rw [Category.assoc, hf0s]) u
    obtain ⟨h1, h2, h3⟩ := hu' (fun _ w => w.Shape Mat κ ∧ w.HasTh (𝟙 _) v ∧
      ∀ x' : Sp K ⟶ F.U.toScheme, TMap w F.univ x' → TMap u F.univ x') ⟨hsh, hth, fun _ h => h⟩
    obtain ⟨x', hx'1, hx'2⟩ := F.obj K (y ≫ f0) u' v h1 h2 hvs
    exact ⟨x', hx'1, h3 x' hx'2⟩
  have hrange : Set.range f0 ⊆ Set.range F.U.ι := by
    rintro q ⟨p, rfl⟩
    obtain ⟨K, _, _, y, p0, hp0⟩ := exists_geomPt S p
    obtain ⟨u, hu⟩ := GlobalTheory.tObj_pull o g _ J b S (Sp K) s' (y ≫ s') y t rfl
    obtain ⟨x', hx', -⟩ := key K y u hu
    refine ⟨x' p0, ?_⟩
    rw [← hp0, ← Scheme.Hom.comp_apply, hx', Scheme.Hom.comp_apply]
  set f := IsOpenImmersion.lift F.U.ι f0 hrange with hfdef
  have hfι : f ≫ F.U.ι = f0 := IsOpenImmersion.lift_fac _ _ _
  have hfs : f ≫ F.U.ι ≫ F.Y.s = s' := by rw [← Category.assoc, hfι, hf0s]
  have hmap : ∀ f' : S ⟶ F.U.toScheme, f' ≫ F.U.ι ≫ F.Y.s = s' → TMap t F.univ f' → ∀ (R : Type) [CommRing R]
      (x : Sp R ⟶ S) (v : Ix g ((n ^ j) ^ 2) → R), t.HasTh x v → SecCoord F.Y.de F.Y.th ((x ≫ f') ≫ F.U.ι) v :=
    fun f' _ hT R _ x v hth =>
      (F.th R (x ≫ f') v).1 ((GlobalTheory.hasTh_iff_of_tmap o g _ J b F.U.toScheme _ F.univ S s' t f' R x v hT).1 hth)
  have hT : TMap t F.univ f := by
    obtain ⟨t2, ht2⟩ := GlobalTheory.tObj_pull o g _ J b F.U.toScheme S (F.U.ι ≫ F.Y.s) s' f F.univ hfs
    have := hS
    have hid : TMap t t2 (𝟙 S) := by
      refine tMap_id_of_geomPt hL hL2 hn hd2 ho fun K _ _ y u hu => ?_
      obtain ⟨x', hx', hxu⟩ := key K y u hu
      have e : x' = y ≫ f := by rw [← cancel_mono F.U.ι, hx', Category.assoc, hfι]
      rw [e] at hxu
      exact TMap.cancel ht2 hxu
    simpa using TMap.comp hid ht2
  refine ⟨f, ⟨hfs, hT⟩, ?_⟩
  rintro f' ⟨hf's, hf'T⟩
  refine hom_ext_affine _ _ fun p => ?_
  obtain ⟨R, _, x, v, hx, hp, hth⟩ := GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g (n ^ j) J b S s' t ho p
  refine ⟨Sp R, x, hx, hp, (cancel_mono F.U.ι).1 ?_⟩
  refine pt_eq_of_secCoord F.Y ?_ (hmap f' hf's hf'T R x v hth) (hmap f hfs hT R x v hth)
  simp only [Category.assoc, hf's, hfs]

end GlobalTheory.ZM.UnivProp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformised
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PeriodObject

variable {E : Type} [Field E] [NumberField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun z i => ty i (a : E) * z i
      map_add' := fun z w => by funext i; simp [mul_add]
      map_smul' := fun c z => by funext i; simp [mul_left_comm] }
  map_one' := by ext z i; simp
  map_mul' a b := by
    ext z i
    show ty i ((a * b : 𝓞 E) : E) * _ = ty i (a : E) * (ty i (b : E) * _)
    push_cast
    rw [map_mul, _root_.mul_assoc]
  map_zero' := by ext z i; simp
  map_add' a b := by ext z i; simp [add_mul]

def imForm (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun z z' w => by simp [hermForm])
    (fun c z w => by simp [hermForm, smul_dotProduct])
    (fun z w w' => by simp [hermForm, Matrix.mulVec_add])
    (fun c z w => by simp [hermForm, Matrix.mulVec_smul, dotProduct_smul])

theorem hermForm_adjoint_of_span (Hm : Matrix (Fin g) (Fin g) ℂ) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    {s : Set (Fin g → ℂ)} (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (F z) w).im = (hermForm Hm z (F' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  have e : (imForm Hm).comp (F.restrictScalars ℝ) = (imForm Hm).compl₂ (F'.restrictScalars ℝ) :=
    LinearMap.ext_on hs fun z hz => LinearMap.ext_on hs fun w hw => h z hz w hw
  have im : ∀ z w, (hermForm Hm (F z) w).im = (hermForm Hm z (F' w)).im := fun z w =>
    LinearMap.congr_fun (LinearMap.congr_fun e z) w
  refine Complex.ext ?_ (im z w)
  have := im (Complex.I • z) w
  simpa [hermForm, smul_dotProduct] using this

theorem weilIs_of_lbIso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L (M.pull (𝟙 A : A ⟶ A).left)) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hw : Out.WeilIs A M n x y c) : Out.WeilIs A L n x y c := by
  have h₁ : LBIso (lbPow L 1) (M.pull (𝟙 A : A ⟶ A).left) :=
    LBIso.trans (DVR.linComb_isLB _ hL _ _) hL (pull_isLB hM _) (lbIso_lbPow_one hL) h
  have := (weilIs_along_hom hG S A A (𝟙 A) L M 1 n T x y c c hA hA hL hM inferInstance h₁
    (by rwa [Category.comp_id, Category.comp_id])).1
  rwa [Nat.cast_one, _root_.mul_one] at this

theorem pelClass_of_period : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), 1 ≤ D.p + D.q → a w = H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → IsPeriod D' ty Q → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → PELClass D a bas ρ em t := by
  intro h₁ h₂ h₃ h₄ E _ _ _ H D o _ g k J b em w w' a bas ρ ty t D' f ν Q Hm hpq hw hρ hty hgen hζ hper hpol
    ⟨u, χ, hAH, hΛ, _, hpt, hF⟩ hprim
  have := t.ab.comm
  have hQ : ∀ (c : 𝓞 E) x, diagAct ty c (Q x) = Q (c • x) := fun c x => funext fun i => (hper.1 c x i).symm
  have hkeep : ∀ c, ∀ z ∈ u.Λ, diagAct ty c z ∈ u.Λ := fun c z hz => by
    obtain ⟨x, rfl⟩ := (hΛ z).1 hz
    exact (hΛ _).2 ⟨c • x, (hQ c x).symm⟩
  obtain ⟨act, hact⟩ := GlobalTheory.T.exists_oAct_of_endo_preserving_lattice h₁ h₂ h₃ h₄ (𝓞 E) t.pol u (diagAct ty) hkeep
  change OAct (𝓞 E) t.A at act
  have hj : ∀ j, act.act (a j) = t.act j := fun j => by
    obtain ⟨F, hFQ, hFe⟩ := hF j
    have e : F.restrictScalars ℝ = (diagAct ty (a j)).restrictScalars ℝ :=
      LinearMap.ext_on_range hpol.2.2.1 fun x => (hFQ x).trans (hQ _ x).symm
    refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h₁ h₂ h₃ h₄ t.pol t.pol t.L t.L u u (diagAct ty (a j)) (hkeep _)).unique
      ⟨act.hom _, hact _⟩ ⟨t.hom j, fun z => ?_⟩
    exact (congrArg u.ex (LinearMap.congr_fun e z).symm).trans (hFe z)
  have hadj : ∀ c, LBIso (cubeLB t.A ![fst t.A t.A ≫ act.act c, snd t.A t.A] t.L)
      (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ act.act (H.bar c)] t.L) := fun c => by
    refine (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint h₁ h₂ h₃ h₄ t.pol u Hm χ _ _ _ _ hAH (act.hom c) (act.hom (H.bar c)) (hact c)
      (hact (H.bar c))).2 (hermForm_adjoint_of_span Hm (diagAct ty c) (diagAct ty (H.bar c)) hpol.2.2.1 ?_)
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have e := D'.adj c x y
    rw [hQ, hQ, hpol.2.2.2.2.2, hpol.2.2.2.2.2, e]
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation h₁.globalFns E H _ t.A act t.L t.ab
    t.isLB (h₃ _ t.pol t.L t.isLB) hadj
  have iso' : LBIso PP.L (t.L.pull (𝟙 t.A : t.A ⟶ t.A).left) := by
    rw [← hw, hj] at iso
    refine LBIso.trans PP.isLB t.isLB (pull_isLB t.isLB _)
      (LBIso.trans PP.isLB (DVR.linComb_isLB _ t.isLB _ _) t.isLB iso hprim.2.2.symm) ?_
    exact (LBIso.chartPull (Geo.Tor.chartPullPull t.L (𝟙 _) (𝟙 _) rfl) (chartPullId t.L) (lbIso_refl t.isLB)).symm
  refine ⟨⟨t.A, isSemiAbelian_of_isAbelianScheme _ t.ab, act, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t.A)), iso', fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · show act.act (a j) ≫ 𝟙 _ = 𝟙 _ ≫ t.act j
    rw [hj, Category.comp_id, Category.id_comp]
  obtain ⟨σ, rfl⟩ : ∃ σ : ℂ →+* K, x = spMap σ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  obtain rfl : σ.comp em = β :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    have := b.unit.map em
    simp [h] at this
  refine ⟨?_, ?_⟩
  · rw [RingHom.comp_apply, hρ]
    exact GlobalTheory.T.determinantCondition_of_diagonalCMAction h₁ h₂ h₃ h₄ E H D t.pol u Hm χ act ty hAH hty hact K σ
  obtain ⟨I, hI⟩ := GlobalTheory.T.exists_tateIso_of_periodMap_genus_alt h₁ h₂ h₃ h₄ E H D D' f ν t.pol u Hm χ act Q hpq hgen hAH hpol.1 hΛ hpol.2.2.2.2.2
    (fun c n x => by
      rw [← hact, map_smul]
      exact congrArg (fun z => u.ex ((n : ℂ)⁻¹ • z)) (hQ c x).symm) K σ
  refine ⟨{ I with isom := fun n hn x y => weilIs_of_lbIso h₁.globalFns t.ab PP.isLB t.isLB iso' (I.isom n hn x y) },
    ?_, fun i => ?_⟩
  · rw [RingHom.comp_apply, hζ]
    exact (hI k hk).1
  · apply Over.OverMorphism.ext
    show (I.ev k _).left ≫ 𝟙 _ = spMap σ ≫ (t.pt i).left
    rw [Category.comp_id, hpt]
    exact (hI k hk).2 _

end GlobalTheory.PeriodObject
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_extension_over_dvr : Out.Laws → Out.Laws2 → ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (s₁ : Sp V ⟶ Sp B) (s' : Sp K ⟶ Sp o) (s₁' : Sp K ⟶ Sp B) (c : SiegPre g k ζ s₁) (c' : SiegPre g k ζ s₁') (t' : TObj g k J b s'), s' = spMap (algebraMap V K) ≫ spMap β → c.Principal → SiegPB c' c (spMap (algebraMap V K)) → TSieg bas bas' t' c' → ∃ t : TObj g k J b (spMap β), TMap t' t (spMap (algebraMap V K)) := by
  first | exact @GlobalTheory.ThetaExtend.exists_tObj_extension | exact GlobalTheory.ThetaExtend.exists_tObj_extension | (intros; apply GlobalTheory.ThetaExtend.exists_tObj_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalPropertyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIdealFamily_universal_property : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (u : TObj g ((n ^ j) ^ 2) J b Y.s), (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' u x) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → ∃! f : S ⟶ Y.MM, f ≫ Y.s = s' ∧ TMap t u f := by
  first | exact @GlobalTheory.FamRep.family_universal | exact GlobalTheory.FamRep.family_universal | (intros; apply GlobalTheory.FamRep.family_universal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapeOfGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevelShape_of_generic_point : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (s : S ⟶ Sp o) (t : TObj g k J b s) (K : Type) [Field K] (x : Sp K ⟶ S) (s' : Sp K ⟶ Sp o) (tK : TObj g k J b s'), Set.range x = {genericPoint S} → TMap tK t x → tK.Shape Mat κ → t.Shape Mat κ := by
  first | exact @GlobalTheory.shape_of_generic | exact GlobalTheory.shape_of_generic | (intros; apply GlobalTheory.shape_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwistAmpleBundleTranslationBundleIsoTranslateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_ampleBundle_translationBundle_iso_translate : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (y : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → Out.RelAmple P.A M → ∃ x : 𝟙_ (Over (Sp K)) ⟶ P.A, LBIso (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ y) * 𝟙 P.A).left] ![1, -1])) (M.pull ((toUnit P.A ≫ x) * 𝟙 P.A).left) := by
  first | exact @GlobalTheory.TwistIsTranslate.twist_iso_translate | exact GlobalTheory.TwistIsTranslate.twist_iso_translate | (intros; apply GlobalTheory.TwistIsTranslate.twist_iso_translate <;> assumption)
end

