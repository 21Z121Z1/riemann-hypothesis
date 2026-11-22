import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilNondegenerateGeneric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.NondegGen

theorem card_hom_lattice (X U : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommGroup U] :
    Nat.card (Multiplicative X →* U) = Nat.card U ^ Module.finrank ℤ X := by
  have e1 : (Multiplicative X →* U) ≃ (X →ₗ[ℤ] Additive U) :=
    (MonoidHom.toAdditiveRight).trans (addMonoidHomLequivInt ℤ).toEquiv
  have e2 := ((Module.finBasis ℤ X).constr ℤ (M' := Additive U)).toEquiv
  rw [Nat.card_congr (e1.trans e2.symm), Nat.card_fun, Nat.card_congr (Additive.toMul : Additive U ≃ U)]
  simp

theorem card_roots (W F : Type) [CommRing W] [Field F] [IsAlgClosed F] (φ : W →+* F) (hφ : Function.Injective φ)
    (N : ℕ) (hN : (N : F) ≠ 0) (h : ∀ z : F, z ^ N = 1 → z ∈ φ.range) : Nat.card (rootsOfUnity N W) = N := by
  haveI : NeZero (N : F) := ⟨hN⟩
  haveI : NeZero N := ⟨fun e => hN (by simp [e])⟩
  refine Eq.trans (Nat.card_congr ?_) (HasEnoughRootsOfUnity.natCard_rootsOfUnity F N)
  refine (Equiv.ofBijective (restrictRootsOfUnity φ N) ⟨fun a b e => ?_, fun z => ?_⟩)
  · have := congrArg (fun u : rootsOfUnity N F => ((u : Fˣ) : F)) e
    simp only [restrictRootsOfUnity_coe_apply] at this
    exact Subtype.ext (Units.ext (hφ this))
  · have hz : ((z : Fˣ) : F) ^ N = 1 := (mem_rootsOfUnity' N _).1 z.2
    obtain ⟨w, hw⟩ := h _ hz
    have hw1 : w ^ N = 1 := hφ (by rw [map_pow, hw, hz, map_one])
    refine ⟨rootsOfUnity.mkOfPowEq w hw1, Subtype.ext (Units.ext ?_)⟩
    rw [restrictRootsOfUnity_coe_apply]
    exact hw

theorem card_hom_torsion (X W : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing W] (N : ℕ) :
    Nat.card (powMonoidHom N : (Multiplicative X →* Wˣ) →* _).ker =
      Nat.card (rootsOfUnity N W) ^ Module.finrank ℤ X := by
  rw [← card_hom_lattice]
  refine Nat.card_congr ⟨fun c => c.1.codRestrict _ fun x => ?_, fun c => ⟨(rootsOfUnity N W).subtype.comp c, ?_⟩,
    fun c => rfl, fun c => rfl⟩
  · exact DFunLike.congr_fun (MonoidHom.mem_ker.1 c.2) x
  · exact MonoidHom.mem_ker.2 (MonoidHom.ext fun x => (c x).2)

theorem card_torsion_ext {GW BF C : Type} [CommGroup GW] [Group BF] [CommGroup C] (N : ℕ) (τ : GW →* BF)
    (j : C →* GW) (hj : Function.Injective j) (hker : ∀ y, τ y = 1 ↔ ∃ c, y = j c)
    (hs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ τ y = x) :
    Nat.card (powMonoidHom N : GW →* GW).ker =
      Nat.card (powMonoidHom N : C →* C).ker * Nat.card {x : BF // x ^ N = 1} := by
  let f := τ.comp (powMonoidHom N : GW →* GW).ker.subtype
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card (powMonoidHom N : GW →* GW).ker := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [← h1]
  congr 1
  · symm
    refine Nat.card_congr (Equiv.ofBijective (fun c => ⟨⟨j c.1, ?_⟩, (hker _).2 ⟨c.1, rfl⟩⟩) ⟨fun a b e => ?_, fun y => ?_⟩)
    · show j c.1 ^ N = 1
      rw [← map_pow]
      exact (congrArg j c.2).trans (map_one j)
    · exact Subtype.ext (hj (congrArg (fun u => u.1.1) e))
    · obtain ⟨c, hc⟩ := (hker y.1.1).1 y.2
      refine ⟨⟨c, hj ?_⟩, Subtype.ext (Subtype.ext hc.symm)⟩
      show j (c ^ N) = _
      rw [map_pow, ← hc, map_one]
      exact y.1.2
  · refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨?_, fun hx => ?_⟩)
    · rintro ⟨y, rfl⟩
      show τ y.1 ^ N = 1
      rw [← map_pow]
      exact (congrArg τ y.2).trans (map_one τ)
    · obtain ⟨y, hy, e⟩ := hs x hx
      exact ⟨⟨y, hy⟩, e⟩

theorem eq_one_of_cubWeil_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    {c : CubicalStr G L} {N : ℕ} {T : Over S} {y : T ⟶ G} {ζ} (h : CubWeil c N 1 y ζ) : ζ = 1 := by
  have h2 := (GlobalTheory.UU.cubWeil_basic S G L c N T).2.1 1 1 y ζ ζ h h
  rw [_root_.mul_one] at h2
  exact mul_eq_left.1 (h2.unique h)

end GlobalTheory.UU.NondegGen

open GlobalTheory.UU.NondegGen in

theorem GlobalTheory.UU.cubWeil_nondegenerate_generic :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {_} {_} _ _ s => ∀ (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ a.B, y ^ N = 1 → CubWeil a.M.c N x y 1) → x = 1 := by
  intro hcard hL V _ _ _ A G _ _ s t a F _ _ _ _ N hN x hx horth
  obtain ⟨W, _, _, _, φ, hφ, hcomp, hW, hloc, hroots, hlift⟩ := GlobalTheory.T.torsion_lift_abelianPart_finite_extension hcard V A G s t a F N hN
  haveI : CharZero V := s.cdvr.2.2
  haveI : CharZero F := charZero_of_injective_ringHom
    (f := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))
    ((algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  haveI := s.semi.separated
  haveI := a.isAb.proper
  let SW : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let σ : TF (R := V) F ⟶ SW := Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    show Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp])
  choose ρf hρ hρu using fun y : SW ⟶ G => GlobalTheory.T.existsUnique_abelianPart_image_adicComplete_point V A G s t a W hW hloc y
  let ρ : (SW ⟶ G) →* (SW ⟶ a.B) := MonoidHom.mk' ρf fun y y' =>
    (hρu _ _ ((GlobalTheory.T.abelianPart_image_one_mul_inv V A G s t a W y y' (ρf y) (ρf y')).2 (hρ y) (hρ y')).1).symm
  obtain ⟨ι', hι, hιs⟩ := GlobalTheory.T.exists_formalTorus_points_semiAbelian_model V A G s t W hW hloc
  let pG : (SW ⟶ G) →* (TF (R := V) F ⟶ G) := preHom σ
  let pB : (SW ⟶ a.B) →* (TF (R := V) F ⟶ a.B) := preHom σ
  have hpG : Function.Injective pG := fun y y' e =>
    GlobalTheory.over_points_ext_of_injective _ G W F φ hφ _ y y' (congrArg (fun q => q.left) e)
  have hpB : Function.Injective pB := fun y y' e =>
    GlobalTheory.over_points_ext_of_injective _ a.B W F φ hφ _ y y' (congrArg (fun q => q.left) e)
  let τ := pB.comp ρ
  have hker : ∀ y, τ y = 1 ↔ ∃ c, y = ι' c := fun y => by
    have e1 : τ y = 1 ↔ ρ y = 1 := map_eq_one_iff pB hpB
    have e2 := GlobalTheory.T.abelianPart_image_eq_one_iff_torus_point V A G s t a W hW hloc y
    rw [e1]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := e2.1 (by have := hρ y; rw [show ρf y = 1 from h] at this; exact this)
      exact ⟨c, (hιs y c).2 hc⟩
    · rintro ⟨c, hc⟩
      exact (hρu y 1 (e2.2 ⟨c, (hιs y c).1 hc⟩)).symm
  have hs : ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ τ y = x := fun x hx => by
    obtain ⟨y, b, hy, hb, e⟩ := hlift x hx
    refine ⟨y, hy, ?_⟩
    have : ρ y = b := (hρu y b hb).symm
    show pB (ρ y) = x
    rw [this]
    exact Over.OverMorphism.ext e
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim V a.B a.isAb
  have hdim := (GlobalTheory.T.dim_eq_abelianPart_dim_add_torus_rank V A G s t g').2 a hg'
  have hB : Nat.card {x : TF (R := V) F ⟶ a.B // x ^ N = 1} = N ^ (2 * g') :=
    GlobalTheory.card_torsion_geometricPoint_of_field hcard _ a.B a.isAb g' hg' F _ N hNF
  have hC := card_hom_torsion s.X W N
  rw [card_roots W F φ hφ N hNF hroots] at hC
  have hH := card_torsion_ext N τ ι' hι hker hs
  rw [hC, hB] at hH
  have hρN : ∀ y : SW ⟶ G, y ^ N = 1 → ρ y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]

  have hpair : ∀ y y' : SW ⟶ G, y ^ N = 1 → y' ^ N = 1 → CubWeil a.M.c N (τ y) (τ y') 1 →
      CubWeil s.P.c N (pG y) (pG y') 1 := fun y y' hy hy' h => by
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil s.P.c hy hy'
    have h1 := (GlobalTheory.T.cubicalWeilPairing_eq_abelianPart_image V A G s t a W hW hloc N y y' (ρ y) (ρ y') ζ (hρ y) (hρ y') (hρN y hy) (hρN y' hy') hζ).comp σ
    have h2 := hζ.comp σ
    rw [h1.unique h] at h2
    exact h2
  have hτN : ∀ y : SW ⟶ G, y ^ N = 1 → τ y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  obtain ⟨y, hy, rfl⟩ := hs x hx
  have hmem := GlobalTheory.UU.mem_of_cubWeil_orthogonal hL V A G s F N hN
    ((powMonoidHom N : (Multiplicative s.X →* Wˣ) →* _).ker.map (pG.comp ι'))
    ((powMonoidHom N : (SW ⟶ G) →* _).ker.map pG) ?_ ?_ ?_ ?_ (pG y) (by rw [← map_pow, hy, map_one]) ?_
  · obtain ⟨c, -, hc⟩ := hmem
    exact (hker y).2 ⟨c, (hpG hc).symm⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ hc).trans (map_one _)
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ hc).trans (map_one _)
  · rw [Subgroup.card_map_of_injective (f := pG.comp ι') (hpG.comp hι), Subgroup.card_map_of_injective hpG, hH, hC, hdim]
    ring
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨y', hy', rfl⟩
    have hcN : ι' c ^ N = 1 := by
      rw [← map_pow]
      exact (congrArg _ hc).trans (map_one _)
    refine hpair (ι' c) y' hcN hy' ?_
    rw [(hker _).2 ⟨c, rfl⟩]
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil a.M.c (one_pow N) (hτN y' hy')
    rwa [eq_one_of_cubWeil_one hζ] at hζ
  · rintro _ ⟨y', hy', rfl⟩
    exact hpair y y' hy hy' (horth _ (hτN y' hy'))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace MapToProj

open MvPolynomial TopologicalSpace SecRingIso LBGerm

variable {R : Type} [CommRing R] {X X' Y Z : Scheme.{0}} {H : LB X} {H' : LB X'} {n : ℕ}
  {s : Fin (n + 1) → H.Sec} {s' : Fin (n + 1) → H'.Sec}

theorem exists_isRatioFamily (s : Fin (n + 1) → H.Sec) (i : Fin (n + 1)) : ∃ r, IsRatioFamily s i r := by
  choose r hr using fun j => exists_quot (s j) (s i) _ le_rfl
  refine ⟨r, fun j k => fn_ext fun y hy => ?_⟩
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, hr j y k hy.1 hy.2, mul_comm]

theorem ratio_gs {i : Fin (n + 1)} {r : Fin (n + 1) → Γ(X, nonzeroLocus (s i))} (hr : IsRatioFamily s i r)
    (φ : Z ⟶ X) (z : Z) (hy : φ z ∈ nonzeroLocus (s i)) {k : H.ι} (hk : φ z ∈ H.U k) (j : Fin (n + 1)) :
    gs φ z _ ((s j).f k) = gs φ z _ (r j) * gs φ z _ ((s i).f k) := by
  have h : φ z ∈ nonzeroLocus (s i) ⊓ H.U k := ⟨hy, hk⟩
  have e := congrArg (gs φ z _) (hr j k)
  rwa [gs_res _ z _ h, gs_mul _ z _ h, gs_res _ z _ h, gs_res _ z _ h] at e

theorem gs_cst (f : X ⟶ Spec (CommRingCat.of R)) (φ : Z ⟶ X) (z : Z) (U : X.Opens) (h : φ z ∈ U) (c : R) :
    gs φ z U (cst f U c) =
      gs (𝟙 Z) z ⊤ ((φ ≫ f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have e := gs_pull (𝟙 Z) φ z ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
  rw [Category.id_comp] at e
  exact (gs_res φ z le_top h _).trans e.symm

theorem ker_le (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R))
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (n + 1) → Γ(X, nonzeroLocus (s i))) (hr' : ∀ i, IsRatioFamily s i (r i))
    (hv : ∀ d, vanishingForms f s d ⊆ vanishingForms f' s' d) (i : Fin (n + 1))
    {r' : Fin (n + 1) → Γ(X', nonzeroLocus (s' i))} (h' : IsRatioFamily s' i r') :
    RingHom.ker (eval₂Hom (cst f _) (r i)) ≤ RingHom.ker (eval₂Hom (cst f' _) r') := by
  intro p hp
  rw [RingHom.mem_ker] at hp ⊢
  obtain ⟨e, F, hF, G, hG⟩ := (ThetaDeform.exists_homogeneous i p).exists
  have hFi : eval₂Hom (cst f _) (r i) F = 0 := by
    rw [eq_add_of_sub_eq hG, map_add, hp, map_mul, map_sub, map_one, eval₂Hom_X', (hr' i).self_eq_one]
    simp
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) F = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr' j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr' j).gs_form f hj hk hF).symm.trans ((hr' i).gs_form f hi hk hF)
    rw [hFi, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose m hm using hn
  have hx : MvPolynomial.X i ^ Finset.univ.sup m * F ∈ vanishingForms f s (Finset.univ.sup m + e) := by
    refine mem_vanishingForms_of_ratios f hc r hr' ((isHomogeneous_X_pow i _).mul hF) fun j => ?_
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := m) (Finset.mem_univ j))
    rw [hb, map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hm j, mul_zero]
  have e₂ := h'.eval_eq_zero f' (hv _ hx)
  rw [eq_add_of_sub_eq hG, map_mul, map_pow, map_add, map_mul, map_sub, map_one, eval₂Hom_X', h'.self_eq_one] at e₂
  simpa using e₂

def Propor (s : Fin (n + 1) → H.Sec) (s' : Fin (n + 1) → H'.Sec) (φ : Z ⟶ X) (ψ : Z ⟶ X') : Prop :=
  ∀ z : Z, (∀ a, φ z ∈ nonzeroLocus (s a) ↔ ψ z ∈ nonzeroLocus (s' a)) ∧
    ∀ a b k k', φ z ∈ H.U k → ψ z ∈ H'.U k' →
      gs φ z _ ((s a).f k) * gs ψ z _ ((s' b).f k') = gs φ z _ ((s b).f k) * gs ψ z _ ((s' a).f k')

theorem Propor.comp {φ : Z ⟶ X} {ψ : Z ⟶ X'} (h : Propor s s' φ ψ) (r : Y ⟶ Z) : Propor s s' (r ≫ φ) (r ≫ ψ) :=
  fun y => ⟨(h (r y)).1, fun a b j j' hj hj' => by
    rw [gs_comp r φ y _ hj, gs_comp r φ y _ hj, gs_comp r ψ y _ hj', gs_comp r ψ y _ hj', ← map_mul, ← map_mul]
    exact congrArg _ ((h (r y)).2 a b j j' hj hj')⟩

theorem Propor.of_local {φ : Z ⟶ X} {ψ : Z ⟶ X'}
    (h : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ Propor s s' (U.ι ≫ φ) (U.ι ≫ ψ)) : Propor s s' φ ψ := fun z => by
  obtain ⟨U, hz, H⟩ := h z
  obtain ⟨y, rfl⟩ : ∃ y : U.toScheme, U.ι y = z := ⟨⟨z, hz⟩, rfl⟩
  refine ⟨(H y).1, fun a b j j' hj hj' => ?_⟩
  have e := (H y).2 a b j j' hj hj'
  rw [gs_comp U.ι φ y _ hj, gs_comp U.ι φ y _ hj, gs_comp U.ι ψ y _ hj', gs_comp U.ι ψ y _ hj',
    ← map_mul, ← map_mul] at e
  exact (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap y)).1 e

theorem Propor.unique (f : X ⟶ Spec (CommRingCat.of R)) {φ₁ φ₂ : Z ⟶ X} {ψ : Z ⟶ X'} (h₁ : Propor s s' φ₁ ψ)
    (h₂ : Propor s s' φ₂ ψ) (e : φ₁ ≫ f = φ₂ ≫ f) {i : Fin (n + 1)} (ha : IsAffineOpen (nonzeroLocus (s i)))
    {r : Fin (n + 1) → Γ(X, nonzeroLocus (s i))} (hr : IsRatioFamily s i r)
    (hs : Function.Surjective (eval₂Hom (cst f _) r)) (hψ : ∀ z, ψ z ∈ nonzeroLocus (s' i)) : φ₁ = φ₂ := by
  have m₁ := fun z => ((h₁ z).1 i).2 (hψ z)
  have m₂ := fun z => ((h₂ z).1 i).2 (hψ z)
  refine hom_ext_affine ha m₁ m₂ fun g z => ?_
  obtain ⟨p, rfl⟩ := hs g
  obtain ⟨k', hk'⟩ := exists_chart_of_mem_nonzeroLocus (hψ z)
  have key : ∀ χ : Z ⟶ X, Propor s s' χ ψ → ∀ j,
      gs χ z _ (r j) * gs ψ z _ ((s' i).f k') = gs ψ z _ ((s' j).f k') := fun χ hχ j => by
    have m := ((hχ z).1 i).2 (hψ z)
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus m
    refine ((mem_nonzeroLocus_iff_pull _ χ z hk).1 m).mul_left_cancel ?_
    rw [← (hχ z).2 j i k k' hk hk', ratio_gs hr χ z m hk j]
    ring
  induction p using MvPolynomial.induction_on with
  | C a => rw [eval₂Hom_C, gs_cst f _ z _ (m₁ z), gs_cst f _ z _ (m₂ z), e]
  | add p q hp hq => rw [map_add, gs_add _ z _ (m₁ z), gs_add _ z _ (m₂ z), hp, hq]
  | mul_X p j hp =>
    rw [map_mul, gs_mul _ z _ (m₁ z), gs_mul _ z _ (m₂ z), hp, eval₂Hom_X']
    exact congrArg _ (((mem_nonzeroLocus_iff_pull _ ψ z hk').1 (hψ z)).mul_right_cancel
      ((key _ h₁ j).trans (key _ h₂ j).symm))

theorem exists_local (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R)) {i : Fin (n + 1)}
    (ha : IsAffineOpen (nonzeroLocus (s i))) {r : Fin (n + 1) → Γ(X, nonzeroLocus (s i))}
    (hr : IsRatioFamily s i r) (hs : Function.Surjective (eval₂Hom (cst f _) r))
    {r' : Fin (n + 1) → Γ(X', nonzeroLocus (s' i))} (hr' : IsRatioFamily s' i r')
    (hk : RingHom.ker (eval₂Hom (cst f _) r) ≤ RingHom.ker (eval₂Hom (cst f' _) r')) :
    ∃ φ : (nonzeroLocus (s' i)).toScheme ⟶ X, φ ≫ f = (nonzeroLocus (s' i)).ι ≫ f' ∧
      Propor s s' φ (nonzeroLocus (s' i)).ι := by
  obtain ⟨φ, hφ, hg⟩ := exists_hom_of_ringHom ha (nonzeroLocus (s' i))
    ((eval₂Hom (cst f _) r).liftOfSurjective hs ⟨_, hk⟩)
  have hp : ∀ p z, gs φ z _ (eval₂Hom (cst f _) r p) =
      gs (nonzeroLocus (s' i)).ι z _ (eval₂Hom (cst f' _) r' p) := fun p z => by
    rw [hg, RingHom.liftOfSurjective_comp_apply]
  have hz : ∀ z : (nonzeroLocus (s' i)).toScheme, (nonzeroLocus (s' i)).ι z ∈ nonzeroLocus (s' i) := fun z => z.2
  refine ⟨φ, hom_ext_spec fun c z => ?_, fun z => ?_⟩
  · have e := hp (C c) z
    rwa [eval₂Hom_C, eval₂Hom_C, gs_cst f _ z _ (hφ z), gs_cst f' _ z _ (hz z)] at e
  · have e : ∀ j, gs φ z _ (r j) = gs (nonzeroLocus (s' i)).ι z _ (r' j) := fun j => by
      have e := hp (MvPolynomial.X j) z
      rwa [eval₂Hom_X', eval₂Hom_X'] at e
    refine ⟨fun a => ?_, fun a b k k' hk hk' => ?_⟩
    · obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (hφ z)
      obtain ⟨k', hk'⟩ := exists_chart_of_mem_nonzeroLocus (hz z)
      rw [mem_nonzeroLocus_iff_pull _ φ z hk, mem_nonzeroLocus_iff_pull _ _ z hk', ratio_gs hr φ z (hφ z) hk a,
        ratio_gs hr' _ z (hz z) hk' a, IsUnit.mul_iff, IsUnit.mul_iff, e,
        and_iff_left ((mem_nonzeroLocus_iff_pull _ φ z hk).1 (hφ z)),
        and_iff_left ((mem_nonzeroLocus_iff_pull _ _ z hk').1 (hz z))]
    · rw [ratio_gs hr φ z (hφ z) hk a, ratio_gs hr φ z (hφ z) hk b, ratio_gs hr' _ z (hz z) hk' a,
        ratio_gs hr' _ z (hz z) hk' b, e, e]
      ring

theorem exists_unit {φ : X' ⟶ X} (h : Propor s s' φ (𝟙 X')) (hc : ⨆ i, nonzeroLocus (s' i) = ⊤) (k : H.ι)
    (k' : H'.ι) : ∃ u : Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ, ∀ j z, φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ ((s j).f k) = (gm (𝟙 X') z _ u).val * gs (𝟙 X') z _ ((s' j).f k') := by
  let V : X'.Opens := (H.pull φ).U (fun _ => k) ⊓ H'.U k'
  let W : Fin (n + 1) → X'.Opens := fun i => V ⊓ nonzeroLocus (s' i)
  have l₁ : ∀ i, W i ≤ φ ⁻¹ᵁ H.U k := fun i x hx => mem_pull.1 hx.1.1
  have l₂ : ∀ i, W i ≤ H'.U k' := fun i x hx => hx.1.2
  have un : ∀ i y, y ∈ W i → IsUnit (gs (𝟙 X') y _ ((s' i).f k')) := fun i y hy =>
    (mem_nonzeroLocus_iff_isUnit _ (l₂ i hy)).1 hy.2
  have hu : ∀ i, IsUnit (resG X' (l₂ i) ((s' i).f k')) := fun i =>
    X'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have := un i y hy
      rw [← gs_res (𝟙 X') y (l₂ i) hy, gs_eq _ y _ hy] at this
      exact this
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, Γ(X', W i), ∀ j (y : X') i, y ∈ W i →
      gs φ y _ ((s j).f k) = gs (𝟙 X') y _ (v i) * gs (𝟙 X') y _ ((s' j).f k') := by
    refine ⟨fun i => resG X' (l₁ i) ((φ.app _).hom ((s i).f k)) * ((hu i).unit⁻¹).val, fun j y i hy => ?_⟩
    have e : gs (𝟙 X') y _ (resG X' (l₁ i) ((φ.app _).hom ((s i).f k)) * ((hu i).unit⁻¹).val) *
        gs (𝟙 X') y _ ((s' i).f k') = gs φ y _ ((s i).f k) := by
      rw [← gs_res (𝟙 X') y (l₂ i) hy ((s' i).f k'), ← gs_mul _ y _ hy, _root_.mul_assoc, (hu i).val_inv_mul,
        _root_.mul_one, gs_res _ y _ hy, gs_pull (𝟙 X') φ y _ (l₁ i hy), Category.id_comp]
    refine (un i y hy).mul_right_cancel ?_
    rw [(h y).2 j i k k' (l₁ i hy) (l₂ i hy), ← e]
    ring
  have cov : ∀ y ∈ V, ∃ i, y ∈ W i := fun y hy => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ y))
    exact ⟨i, hy, hi⟩
  obtain ⟨c, hc', -⟩ := DVR.sec_glue V W (fun _ => inf_le_left) (fun y hy => Opens.mem_iSup.2 (cov y hy)) v
    (fun a b => fn_ext fun y hy => by
      rw [gs_res _ y _ hy, gs_res _ y _ hy]
      exact (un a y hy.1).mul_right_cancel ((hv a y a hy.1).symm.trans (hv a y b hy.2)))
  have hcv : ∀ j y, y ∈ V → gs φ y _ ((s j).f k) = gs (𝟙 X') y V c * gs (𝟙 X') y _ ((s' j).f k') :=
    fun j y hy => by
      obtain ⟨i, hi⟩ := cov y hy
      rw [hv j y i hi, ← hc' i, gs_res _ y _ hi]
  have uc : IsUnit c := X'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨i, hi⟩ := cov y hy
    have := (mem_nonzeroLocus_iff_pull _ φ y (l₁ i hi)).1 (((h y).1 i).2 hi.2)
    rw [hcv i y hy] at this
    have := isUnit_of_mul_isUnit_left this
    rw [gs_eq _ y _ hy] at this
    exact this
  refine ⟨uc.unit, fun j z hk hk' => ?_⟩
  have hz : z ∈ V := ⟨mem_pull.2 hk, hk'⟩
  rw [← gs_unit _ z V hz]
  exact hcv j z hz

theorem exists_iso {φ : X' ⟶ X} (h : Propor s s' φ (𝟙 X')) (hc : ⨆ i, nonzeroLocus (s' i) = ⊤) :
    ∃ w : LB.Iso H' (H.pull φ), w.IsGen ∧ ∀ j z k k', φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ ((s j).f k) = (gw w (𝟙 X') z k k').val * gs (𝟙 X') z _ ((s' j).f k') := by
  choose u hu using fun k k' => exists_unit h hc k k'
  refine ⟨⟨fun p => u (p.1 PUnit.unit) p.2⟩, ?_, fun j z k k' hk hk' => hu k k' j z hk hk'⟩
  rintro ⟨J, k⟩ ⟨J', k'⟩
  apply unit_ext
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have this : gm (𝟙 X') x _ (u (J PUnit.unit) k) = gm (𝟙 X' ≫ φ) x _ (H.g (J PUnit.unit) (J' PUnit.unit)) *
      (gm (𝟙 X') x _ (H'.g k k'))⁻¹ * gm (𝟙 X') x _ (u (J' PUnit.unit) k') := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ x))
    have e := hu _ k i x hj hx.1.2
    rw [gs_compat (s i) φ x hj hj', gs_compat (s' i) (𝟙 X') x hx.1.2 hx.2.2, hu _ k' i x hj' hx.2.2,
      ← _root_.mul_assoc, ← _root_.mul_assoc] at e
    have e' := ((mem_nonzeroLocus_iff_isUnit _ hx.2.2).1 hi).mul_right_cancel e
    rw [Category.id_comp, mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact Units.ext e'.symm
  rw [← gm_div_g (𝟙 X') x _ _ k k' hj hj' hx.1.2 hx.2.2] at this
  exact (gm_res _ x _ hx _).trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

end MapToProj

open MapToProj in

theorem exists_hom_of_veryAmpleBy : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → (⨆ i, nonzeroLocus (s' i) = ⊤) → (∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F) = 0) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (f') ((H').U k)) (fun j => (s' j).f k) (F) = 0)) → ∃ (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), φ ≫ f = f' ∧ w.IsGen ∧ (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) := by
  intro R _ X f H n s _ ⟨hc, hs⟩ X' f' H' s' _ hc' hv
  choose ha r hr hsur using hs
  have hv' : ∀ d, vanishingForms f s d ⊆ vanishingForms f' s' d := fun d F hF => ⟨hF.1, hv d F hF.1 hF.2⟩
  choose r' hr' using exists_isRatioFamily s'
  choose φ hf hφ using fun i => exists_local f f' (ha i) (hr i) (hsur i) (hr' i) (ker_le f f' hc ha r hr hv' i (hr' i))
  let 𝒰 := X'.openCoverOfIsOpenCover (fun i => nonzeroLocus (s' i)) hc'
  have hcomp : ∀ i j : Fin (n + 1), pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ φ i =
      pullback.snd _ _ ≫ φ j := fun i j =>
    ((hφ i).comp _).unique f (by rw [pullback.condition]; exact (hφ j).comp _)
      (by rw [Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]) (ha i) (hr i) (hsur i)
      fun z => (pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι z).2
  have hΦ : ∀ i : Fin (n + 1), (nonzeroLocus (s' i)).ι ≫ 𝒰.glueMorphisms φ hcomp = φ i :=
    fun i => 𝒰.ι_glueMorphisms φ hcomp i
  have hP : Propor s s' (𝒰.glueMorphisms φ hcomp) (𝟙 X') := Propor.of_local fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc'.ge (Set.mem_univ x))
    exact ⟨_, hi, by rw [hΦ, Category.comp_id]; exact hφ i⟩
  obtain ⟨w, hw, H⟩ := exists_iso hP hc'
  refine ⟨_, w, 𝒰.hom_ext _ _ fun i => ?_, hw, H⟩
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (hΦ i))).trans (hf i)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingAutOfRelAmple
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_iso_of_sectionRing_aut_of_relAmple : ∀ (K : Type) [CommRing K] (X : Over (Spec (CommRingCat.of K))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 L n ≃ H0 L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : K) (a b d : H0 L n), (∀ j, d.f j = a.f j + resTop _ (scal X.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal X.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L n) (b : H0 L m) (d : H0 L (n + m)), (∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from d.f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from a.f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from b.f j)) → ∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ n hn a).f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ m hm b).f j)) → ∃ Φ₀ : X ≅ X, ∃ w : LB.Iso L (L.pull Φ₀.hom.left), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 L n), (∀ (Z : Scheme.{0}) (r : Z ⟶ X.left) (z : Z) (p : Fin 1 → L.ι) (q : Fin 1 → L.ι), (∀ κ, (Φ₀.hom.left) ((fun _ : Fin 1 => 𝟙 X.left) κ (r z)) ∈ L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 X.left) κ (r z) ∈ L.U (q κ)) → Geo.Tor.gs (r ≫ Φ₀.hom.left) z (LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 X.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) q) ((a).f q)) := by
  intro K _ X _ L hL hA θ hlin hmul
  have h := isAmpleLB_of_relAmple_of_isAffine X hL hA
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  obtain ⟨-, m, hm, M, s, hs⟩ := isAffineOpen_nonzeroLocus_of_relAmple K X L hL hA 1 le_rfl
  have hN : 1 ≤ 1 * m := by omega
  have haff := (isAffineOpen_nonzeroLocus_of_relAmple K X L hL hA (1 * m) hN).1
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_sectionRing_equiv K X X L L hL hL θ hlin hmul
    ⟨1 * m, hN, H0 L (1 * m), id,
      top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup (fun a : H0 L (1 * m) => nonzeroLocus a) (s i))),
      top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup_of_le ((θ (1 * m) hN).symm (s i))
        (congrArg nonzeroLocus ((θ (1 * m) hN).apply_symm_apply (s i))).ge)),
      fun a => ⟨haff _, haff _⟩⟩
  exact ⟨Φ, exists_iso_of_sectionRing K X X L L hL hL θ hlin hmul Φ.hom.left hΦ
    (exists_sec_succ_of_relAmple K X L hL hA)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquivStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_iso_of_sectionRing_equiv_alt : ∀ (R : Type) [CommRing R] (X X' : Over (Spec (CommRingCat.of R))) [CompactSpace X.left] [QuasiSeparatedSpace X.left] [CompactSpace X'.left] [QuasiSeparatedSpace X'.left] (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : R) (a b d : H0 L' n), (∀ j, d.f j = a.f j + resTop _ (scal X'.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal X.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L' n) (b : H0 L' m) (d : H0 L' (n + m)), (∀ j : Fin 1 → L'.ι, (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from d.f j) = (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from a.f j) * (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from b.f j)) → ∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ n hn a).f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ m hm b).f j)) → (∃ (N : ℕ) (hN : 1 ≤ N) (κ : Type) (s : κ → H0 L' N), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ (⨆ i, nonzeroLocus (θ N hN (s i)) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧ IsAffineOpen (nonzeroLocus (θ N hN (s i)))) → ∃ Φ : X' ≅ X, (∀ (n : ℕ) (hn : 1 ≤ n) (a b : H0 L' n), Φ.hom.left ⁻¹ᵁ nonzeroLocus (θ n hn b) = nonzeroLocus b ∧ ∀ (x : X'.left) (j : Fin 1 → L.ι) (j' : Fin 1 → L'.ι), x ∈ nonzeroLocus b → Φ.hom.left x ∈ L.U (j 0) → x ∈ L'.U (j' 0) → Geo.Tor.gs Φ.hom.left x _ ((θ n hn a).f j) * Geo.Tor.gs (𝟙 X'.left) x _ (b.f j') = Geo.Tor.gs Φ.hom.left x _ ((θ n hn b).f j) * Geo.Tor.gs (𝟙 X'.left) x _ (a.f j')) := by
  first | exact @GlobalTheory.exists_iso_of_sectionRing_equiv | exact GlobalTheory.exists_iso_of_sectionRing_equiv | (intros; apply GlobalTheory.exists_iso_of_sectionRing_equiv <;> assumption)
end

