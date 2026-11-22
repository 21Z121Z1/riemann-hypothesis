import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFamily

section Pairing

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}

theorem weilIs_pow_left (hW : Out.WeilSt) {n : ℕ} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) (m : ℕ) : Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := by
  induction m with
  | zero => rwa [zero_add, pow_one, pow_one]
  | succ m ih =>
    rw [pow_succ x, pow_succ c]
    exact (hW S P n T).2.1 _ _ _ _ _ ih h

theorem weilIs_lower (hW : Out.WeilSt) {n m : ℕ} (hm : 0 < m) (hu : IsUnit ((n * m : ℕ) : Γ(T.left, ⊤)))
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * m) = 1) (hy : y ^ (n * m) = 1)
    (h : Out.WeilIs P.A P.L ((n * m : ℕ) : ℤ) x y c) : Out.WeilIs P.A P.L n (x ^ m) (y ^ m) (c ^ m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h₁ := CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₁
  exact ((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁

theorem eq_one_of_weilIs_one {K : Type} [Field K] (hW : Out.WeilSt) {x : Sp K ⟶ S} {n : ℕ}
    {y : Over.mk x ⟶ P.A} {c : Kˣ} (h : Out.WeilIs P.A P.L n 1 y (unitOn c)) : c = 1 := by
  have h₁ := (hW S P n _).2.1 _ _ _ _ _ h h
  rw [_root_.mul_one] at h₁
  have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
  exact mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)

end Pairing

theorem weilIs_of_lbIso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L (M.pull (𝟙 A : A ⟶ A).left)) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hw : Out.WeilIs A M n x y c) : Out.WeilIs A L n x y c := by
  have h₁ : LBIso (lbPow L 1) (M.pull (𝟙 A : A ⟶ A).left) :=
    LBIso.trans (DVR.linComb_isLB _ hL _ _) hL (pull_isLB hM _) (lbIso_lbPow_one hL) h
  have := (weilIs_along_hom hG S A A (𝟙 A) L M 1 n T x y c c hA hA hL hM inferInstance h₁
    (by rwa [Category.comp_id, Category.comp_id])).1
  rwa [Nat.cast_one, _root_.mul_one] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g k : ℕ} {J : Type}
  {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {o : Type} [CommRing o] {b : TBase o k} {em : o →+* ℂ} {ρ : o}
  {S : Scheme.{0}} {s : S ⟶ Sp o}

theorem exists_fibre (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s} {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (x : Sp K ⟶ S) (tx : TObj g k J b (x ≫ s)) (τ : SAB H (Sp K)),
      p ∈ Set.range x ∧ TMap tx t x ∧ IsPEL D a bas ρ tx τ := by
  obtain ⟨K, _, x, hx, K₀, _, β, i, j, t₀, tx, tc, hj, hs, m₁, m₂, m₃, τ, hτ⟩ := hp
  obtain ⟨τ₀, h₀⟩ := GlobalTheory.T.pelStructure_descends_field_extension hL E H D g k J a bas o b ρ K₀ ℂ j β _ t₀ tc τ hcl
    (by rw [← hj]; exact Spec.map_comp _ _) m₃ hτ
  obtain ⟨τ', h'⟩ := PELPull.isPEL_pull E H D g k J a bas o b ρ _ _ _ _ _ t₀ tx τ₀ hs.symm m₂ h₀
  have : CharZero K₀ := j.charZero
  exact ⟨K, inferInstance, (i.charZero_iff i.injective).1 inferInstance, x, tx, τ', hx, m₁, h'⟩

theorem exists_fibre_map (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s} {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (x : Sp K ⟶ S) (τ : SAB H (Sp K)) (ψ : τ.G.left ⟶ t.A.left),
      p ∈ Set.range x ∧ IsGrpPullback τ.G t.A x ψ ∧ LBIso τ.PP.L (t.L.pull ψ) ∧
      (∀ j, (τ.act.act (a j)).left ≫ ψ = ψ ≫ (t.act j).left) ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (y : Sp Ω ⟶ Sp K) (β : o →+* Ω), y ≫ x ≫ s = spMap β →
        DetCond D τ.act y (β ρ) ∧ ∃ I : TateIso D Ω (Over.mk y ⟶ τ.G) (fun c z => z ≫ τ.act.act c)
            (fun n z z' c => Out.WeilIs τ.G τ.PP.L n z z' (unitOn c)),
          (I.ζ k : Ω) = β b.ζ ∧ ∀ i, (I.ev k (bas (Pi.single i 1))).left ≫ ψ = (y ≫ x) ≫ (t.pt i).left := by
  obtain ⟨K, _, _, x, tx, τ, hx, ⟨ψ, hψ, hψL, hpt, hact⟩, φ, hφ, hφL, hφa, hgeom⟩ := exists_fibre hL hcl hp
  refine ⟨K, inferInstance, inferInstance, x, τ, φ.hom.left ≫ ψ, hx,
    ((isGrpPullback_of_iso φ).comp hψ).congr (Category.id_comp x) rfl,
    hφL.trans τ.PP.isLB (pull_isLB tx.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL _ rfl),
    fun j => ?_, fun Ω _ _ _ y β hy => ?_⟩
  · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (tx.act j).left :=
      congrArg (fun z => z.left) (hφa j)
    rw [← Category.assoc, h₁, Category.assoc, hact, Category.assoc]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom Ω y β hy
    refine ⟨hdet, I, hI, fun i => ?_⟩
    have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = y ≫ (tx.pt i).left :=
      congrArg (fun z => z.left) (hA i)
    rw [← Category.assoc, h₁, Category.assoc, hpt, Category.assoc]

theorem exists_geom (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s}
    (r : OAct (𝓞 E) t.A)
    (hr : ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ t.A.left) (act : OAct (𝓞 E) G),
      IsGrpPullback G t.A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (t.act j).left) →
      ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left) {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K),
      p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D r x (β ρ) ∧
      ∃ I : TateIso D K (Over.mk x ⟶ t.A) (fun c z => z ≫ r.act c)
          (fun n z z' c => Out.WeilIs t.A t.L n z z' (unitOn c)),
        (I.ζ k : K) = β b.ζ ∧ ∀ i, I.ev k (bas (Pi.single i 1)) =
          (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i := by
  have := t.ab.comm
  obtain ⟨K, _, _, x, τ, ψ, ⟨q, hq⟩, hψ, hψL, hact, hgeom⟩ := exists_fibre_map hL hcl hp
  have hc := hr _ x τ.G ψ τ.act hψ hact
  let y : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
  obtain ⟨β, hβ⟩ : ∃ β : o →+* AlgebraicClosure K, y ≫ x ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ x ≫ s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨hdet, I, hI, hA⟩ := hgeom _ y β hβ
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, y ≫ x, β,
    ⟨(default : PrimeSpectrum (AlgebraicClosure K)), ?_⟩, (Category.assoc _ _ _).trans hβ, fun σ => ?_,
    ObjPull.tateMove (ObjPull.pushEquiv hψ (Over.mk y)).symm (fun c z => ?_) (fun n z z' c hz => ?_) I, hI,
    fun i => Over.OverMorphism.ext (hA i)⟩
  · exact (Scheme.Hom.comp_apply y x _).trans ((congrArg x (Subsingleton.elim (α := PrimeSpectrum K) _ _)).trans hq)
  · rw [← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ,
      ← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ]
    exact hdet σ
  · obtain ⟨z, rfl⟩ := (ObjPull.pushEquiv hψ (Over.mk y)).surjective z
    rw [MulEquiv.symm_apply_eq, MulEquiv.symm_apply_apply]
    apply Over.OverMorphism.ext
    show (z.left ≫ _) ≫ _ = (z.left ≫ _) ≫ _
    rw [Category.assoc, ← hc, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm _ _ t.A τ.G x ψ t.L τ.PP.L t.isLB τ.PP.isLB hψ hψL (Over.mk y) n _ _ z z' _
      (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z).symm
      (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z').symm).1 hz

theorem exists_isPEL_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (w w' : J), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), em ρ = H.rt0 → Function.Injective em → Dense (fromSet em (PELClass (b := b) D a bas ρ em) t) → ∃ τ : SAB H S, IsPEL D a bas ρ t τ := by
  intro hL _ hcube E _ _ _ H D g J a bas w w' _ _ hw _ hcl k o _ b em ρ S _ _ s t hρ hem hd
  have := t.ab.comm
  obtain ⟨r, hra, hr⟩ := GlobalTheory.T.oAct_spread_from_dense_fibres_abelianScheme (𝓞 E) J a S t.A t.act hcl t.ab t.hom (hd.mono fun p hp => by
    obtain ⟨K, _, _, x, τ, ψ, hx, hψ, -, hact, -⟩ := exists_fibre_map hL hcl hp
    exact ⟨K, inferInstance, x, τ.G, inferInstance, ψ, τ.act, hx, hψ, hact⟩)
  have hadj := fun c => GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres hL.globalFns S t.A t.L (r.act c) (r.act (H.bar c)) t.ab t.isLB t.ample (r.hom _)
    (r.hom _) (hd.mono fun p hp => by
      obtain ⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩ := exists_fibre_map hL hcl hp
      have hc := hr _ x τ.G ψ τ.act hψ hact
      exact ⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, _, hx, hψ, τ.PP.isLB, hψL, hc _, hc _,
        τ.adj c⟩)
  have hprim := GlobalTheory.T.lbIso_cube_graph_of_dense_fibres hL.globalFns S t.A t.L (r.act H.w0) t.ab t.isLB t.ample t.rigid (r.hom _)
    (hd.mono fun p hp => by
      obtain ⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩ := exists_fibre_map hL hcl hp
      have hc := hr _ x τ.G ψ τ.act hψ hact
      exact ⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, hx, hψ, τ.PP.isLB, hψL, hc _, τ.prim⟩)
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation hL.globalFns E H _ t.A r t.L t.ab
    t.isLB (hcube _ t.pol t.L t.isLB) hadj
  have iso' : LBIso PP.L (t.L.pull (𝟙 t.A : t.A ⟶ t.A).left) := by
    refine LBIso.trans PP.isLB t.isLB (pull_isLB t.isLB _)
      (LBIso.trans PP.isLB (DVR.linComb_isLB _ t.isLB _ _) t.isLB iso hprim.symm) ?_
    exact (LBIso.chartPull (Geo.Tor.chartPullPull t.L (𝟙 _) (𝟙 _) rfl) (chartPullId t.L) (lbIso_refl t.isLB)).symm
  refine ⟨⟨t.A, isSemiAbelian_of_isAbelianScheme _ t.ab, r, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t.A)), iso', fun j => ?_, fun K _ _ _ x β hx => ⟨?_, ?_⟩⟩
  · show r.act (a j) ≫ 𝟙 _ = 𝟙 _ ≫ t.act j
    rw [hra, Category.comp_id, Category.id_comp]
  · refine GlobalTheory.T.determinantCondition_spreads_of_dense_points E H D S t.A g r o s ρ t.dim (hem ?_) (hd.mono fun p hp => ?_) K x β hx
    · rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast]
    · obtain ⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩ := exists_geom hL hcl r hr hp
      exact ⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    have := b.unit.map em
    simp [h] at this
  have hcard : ∀ n, 0 < n → Nat.card {z : Over.mk x ⟶ t.A // z ^ n = 1} = n ^ Module.finrank ℤ D.La := fun n hn => by
    rw [← bas.finrank_eq, Module.finrank_fin_fun]
    exact (hL.mulN S t.pol n hn).2.2.2.2 K x (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.T.tateIsometry_of_finiteLevel_isometries E H D K (Over.mk x ⟶ t.A) (fun c z => z ≫ r.act c)
    (fun n z z' c => Out.WeilIs t.A t.L n z z' (unitOn c)) k (β b.ζ) _ (fun i => bas (Pi.single i 1))
    (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i) hk
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m z z' c hn hm hz hz' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact weilIs_lower t.pol hL.weil hm u' hz hz' h)
    (fun m hm => by
      have hn := Nat.mul_pos hk hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_level_isometry_of_dense_geometric_points hL E H D S t.pol r.act o s b.ζ _
        (fun i => bas (Pi.single i 1)) t.pt (k * m) m hn (hd.mono fun p hp => by
          obtain ⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩ := exists_geom hL hcl r hr hp
          exact ⟨K, inferInstance, x, β, I.ζ (k * m), I.ev (k * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn,
            I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn,
            by rw [← h₃, ← I.ζ_pow k m hk hm, Units.val_pow_eq_pow_val],
            fun i => (I.tower k m hk hm _).trans (h₄ i)⟩) K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n E H D K (Over.mk x ⟶ t.A)
        (fun z z' c => Out.WeilIs t.A t.L (k * m : ℕ) z z' (unitOn c)) (k * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => eq_one_of_weilIs_one t.pol hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, h₇⟩)
  exact ⟨{ I with isom := fun n hn z z' => weilIs_of_lbIso hL.globalFns t.ab PP.isLB t.isLB iso' (I.isom n hn z z') },
    hI, fun i => (Category.comp_id _).trans (hA i)⟩

end GlobalTheory.PELFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDense
section
noncomputable section

namespace GlobalTheory.MulDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem comp_eq_one_of_kTriv_pull {S S' : Scheme.{0}} {f : S' ⟶ S}
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L')
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (x : Over.mk t ⟶ A)
    (hx : ∀ p : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, p ∈ V ∧
      ∃ c : LB.Gen ((translDiff A L x).pull ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι), c.IsGen)
    {R' : CommRingCat.{0}} (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S') (sq : g ≫ t = t' ≫ f) :
    g ≫ x.left = g ≫ (1 : Over.mk t ⟶ A).left := by
  obtain ⟨w, hw⟩ := hw
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact congrArg (fun q => q.left) e₂

theorem kTriv_of_locally {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (H : ∀ s : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S), IsOpenImmersion f ∧ IsAffineHom f ∧ s ∈ Set.range f ∧
      KTriv ((Over.pullback f).obj A) (L.pull (pullback.fst A.hom f))) : KTriv A L := by
  intro R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ A).left fun p => ?_)
  obtain ⟨S', f, h₁, h₂, ⟨s, hs⟩, hK⟩ := H (t p)
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let g := (pullback t f).isoSpec.inv ≫ pullback.fst t f
  have e := comp_eq_one_of_kTriv_pull (isGrpPullback_pullback A f) hL (pull_isLB hL _)
    (PolBaseChange.lbIso_refl (pull_isLB hL _)) hK t x hx g ((pullback t f).isoSpec.inv ≫ pullback.snd t f)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have e' : pullback.fst t f ≫ x.left = pullback.fst t f ≫ (1 : Over.mk t ⟶ A).left := by
    rw [← cancel_epi (pullback t f).isoSpec.inv, ← Category.assoc, ← Category.assoc]
    exact e
  refine ⟨(pullback.fst t f).opensRange, ?_, ?_⟩
  · show p ∈ Set.range (pullback.fst t f)
    rw [Scheme.Pullback.range_fst]
    exact ⟨s, hs⟩
  · rw [← cancel_epi (pullback.fst t f).isoOpensRange.hom, ← Category.assoc, ← Category.assoc]
    erw [Scheme.Hom.isoOpensRange_hom_ι]
    exact e'

theorem kTriv_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] {L L' : LB A.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : LBIso L L') (hK : KTriv A L) : KTriv A L' := by
  obtain ⟨w, hw⟩ : LBIso L' (L.pull (Iso.refl A).hom.left) :=
    h.symm.chartPull (Geo.Tor.chartPullId L') (Geo.Tor.chartPullPull L (𝟙 _) (𝟙 _) rfl)
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  exact kTriv_pull (isGrpPullback_of_iso (Iso.refl A)) hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.MulDescent

namespace GlobalTheory.MulDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_polarisation_of_veryDense : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (P : Set (Ideal R)) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Fin (2 * g) → ZMod m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  intro h₁ h₂ R _ _ _ A _ g m M P pt hA hg hm hu hM hamp hP hpt hbas hfib
  obtain ⟨L, hL, hrig, hsym, hLa, hiso⟩ := GlobalTheory.OddDescent.exists_descended h₁ h₂ R A g m M pt hA hg hm hu hM hamp hpt hbas (by
    intro f hf
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
    by_contra hn
    obtain ⟨p, hp, hp', -, hfp⟩ := hP q f hq hn
    exact hfp (hf p (hfib p hp) hp'))
  refine ⟨L, hL, hrig, hsym, hLa, kTriv_of_locally hL fun s => ?_, hiso⟩
  have hs : (s : PrimeSpectrum R).asIdeal.IsPrime := (s : PrimeSpectrum R).isPrime
  obtain ⟨p, hp, -, hle, -⟩ := hP (s : PrimeSpectrum R).asIdeal 1 hs
    (fun h => hs.ne_top ((Ideal.eq_top_iff_one _).2 h))
  obtain ⟨K, _, _, x, Pl, φ, hker, hφ, hw⟩ := hfib p hp
  obtain ⟨f, hf, H⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K x Pl.A φ hA hL hLa hφ
    (kTriv_of_lbIso Pl.isLB (pull_isLB hL _) (hiso K x Pl φ hφ hw) Pl.ktriv)
  have hfs : f ∉ (s : PrimeSpectrum R).asIdeal := fun h => hf (by
    have := hle h
    rwa [← hker, RingHom.mem_ker] at this)
  have ho : IsOpenImmersion (spMap (algebraMap R (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
  refine ⟨_, spMap (algebraMap R (Localization.Away f)), ho, inferInstance, ?_,
    H (Localization.Away f) (algebraMap R _) _ _ (IsLocalization.Away.algebraMap_isUnit f)
      (isGrpPullback_pullback A _)⟩
  have : s ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hfs
  exact this

end GlobalTheory.MulDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareLevelWithGivenThetaPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_level_with_given_thetaPoint : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → VeryDense {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), RingHom.ker x = q ∧ t'.HasTh (𝟙 _) (fun a => x (v a)) ∧ (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left)} → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), t'.HasTh (𝟙 _) (fun a => x (v a)) → (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) → TMap t' t (spMap x) := by
  first | exact @GlobalTheory.LevelTheta.exists_level_with_theta_point | exact GlobalTheory.LevelTheta.exists_level_with_theta_point | (intros; apply GlobalTheory.LevelTheta.exists_level_with_theta_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_hom_extension_semiAbelian_normal_base_alt : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (X U : Scheme.{0}) (j : U ⟶ X), (IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f := by
  first | exact @GlobalTheory.existsUnique_hom_extension_semiAbelian_normal | exact GlobalTheory.existsUnique_hom_extension_semiAbelian_normal | (intros; apply GlobalTheory.existsUnique_hom_extension_semiAbelian_normal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalFullLevelOfPelThetaFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_fullLevel_of_pelThetaFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  first | exact @GlobalTheory.exists_famCore_of_thetaFam | exact GlobalTheory.exists_famCore_of_thetaFam | (intros; apply GlobalTheory.exists_famCore_of_thetaFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

theorem point_eq_iff_isometry_closed :
    ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' D'' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t' : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ)) (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y' ≫ Xo.s = spMap σ ∧ IsPeriod D'' ty P' ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y' ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ (∀ v : epsPt y' ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧ (∀ z, e' z = 1 ↔ z ∈ (P').range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D''.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D''.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P' (t' a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P' (t' a))) → (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞 E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D''.EF (gam a) (gam b) = D'.EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧ (∀ a, ∃ x, gam (t a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a)) :=
  fun hT hL =>
    point_eq_iff_isometry hT hL (GlobalTheory.exists_isMonHom_of_map_lattice hT hL) (GlobalTheory.T.lambdaBundleIso_of_primeToP_weilPairings hL)
      GlobalTheory.obj_pull GlobalTheory.ObjMaps.id_comp_cancel GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym
      (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel)

end GlobalTheory.UnifPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_siegel_of_generic_principal_special_ample : Out.Laws → Out.Laws2 → ∀ (h k : ℕ), Odd k → 3 ≤ k → ∀ (B : Type) [CommRing B] (ζ : B) (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsLocalRing O] [Algebra O C], IsUnitBall O C → ∀ p : ℕ, p.Prime → ‖(p : C)‖ < 1 → ∀ (β : B →+* O) (c : SiegPre h k ζ (spMap β)), (∃ c' : SiegPre h k ζ (spMap (algebraMap O C) ≫ spMap β), SiegPB c' c (spMap (algebraMap O C)) ∧ c'.Principal) → Out.RelAmple (Over.mk (pullback.snd c.A.hom (spMap (IsLocalRing.residue O)))) (c.diag.pull (pullback.fst c.A.hom (spMap (IsLocalRing.residue O)))) → c.Principal := by
  first | exact @GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special | exact GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special | (intros; apply GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvrStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupK_trivial_of_principal_genericFibre_dvr : Laws → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L → KTriv B M.L.L := by
  first | exact @GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | exact GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | (intros; apply GlobalTheory.KTrivSpread.kTriv_of_generic_fibre <;> assumption)
end

