import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0285
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0294
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0302
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToroidalFlagSmoothProjective
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FlagSmooth

open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
  GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_gChart_of_flagCover {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (x : Y.X) :
    ∃ M : GChart Y, x ∈ M.U := by
  obtain ⟨z, rfl⟩ := GlobalTheory.BaseVar.surjective_π X x
  have hz : z ∈ (⨆ k, X.F.U k) := by rw [X.F.cover]; trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hz
  exact ⟨X.F.M k, X.F.le k hk⟩

theorem nonempty_atlas_of_cover (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F))
    (hG : ∀ x : Y.X, ∃ M : GChart Y, x ∈ M.U) : Nonempty (Atlas Y p) := by
  classical
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsReduced Y.X := by
    have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      have := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, N, σ, A, C, haff, hle, hCA, htw⟩ := GlobalTheory.TwistEmb.exists_twist_embedding c.F Y.X Y.s (GChart Y)
    (fun j => j.U) (fun j => j.n) (fun j j' => chg j.toMChart j'.toMChart) Y.proj
    (fun x => hG x)
    (fun K _ w j hw => by
      have hh : ⊤ ≤ w ⁻¹ᵁ (j.U ⊓ j.U) := GlobalTheory.TwistEmb.le_inf' w hw hw
      show (chg j.toMChart j.toMChart).map (valF w (j.U ⊓ j.U)) = 1
      rw [map_valF_eq_ev w _ hh, chg_map _ _ w hw hw hh, Module.Basis.toMatrix_self])
    (fun K _ w j j' j'' h1 h2 h3 => by
      show (chg j.toMChart j'.toMChart).map (valF w (j.U ⊓ j'.U)) *
        (chg j'.toMChart j''.toMChart).map (valF w (j'.U ⊓ j''.U)) =
        (chg j.toMChart j''.toMChart).map (valF w (j.U ⊓ j''.U))
      rw [map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h2), map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h2 h3),
        map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h3), chg_map _ _ w h1 h2, chg_map _ _ w h2 h3,
        chg_map _ _ w h1 h3, Module.Basis.toMatrix_mul_toMatrix])
  have hcovL : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x => exists_chart L.isLB x
  have hk : ∀ x : Y.X, ∃ i, ∃ k : ECh Y p, k.M = σ i ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := hcovL x
    obtain ⟨k, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_eigenChart_affineOpen_within E H Dw l Xo c Y p (σ i) x (hle i hi) (L.U i) hi
    exact ⟨i, k, h1, h2, h3, h4⟩
  choose ix kx hkM hxk haffk hlek using hk
  have hc : IsCompact (Set.univ : Set Y.X) := by
    have e : (Set.univ : Set Y.X) = ⋃ i, ((L.U i : Y.X.Opens) : Set Y.X) :=
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcovL x)).symm
    rw [e]
    exact isCompact_iUnion fun i => (haff i).isCompact
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => ((kx x).V : Set Y.X)) (fun x => (kx x).V.isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxk x⟩)
  have hUM : ∀ i i', L.U i ⊓ L.U i' ≤ (σ i').U ⊓ (σ i).U := fun i i' =>
    le_inf (inf_le_right.trans (hle i')) (inf_le_left.trans (hle i))
  exact ⟨{
    B := t
    fin := inferInstance
    k := fun b => kx b.1
    aff := fun b => haffk b.1
    cov := fun x => by
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact ⟨⟨z, hz⟩, hxz⟩
    N := N
    A := fun b => trA (hkM b.1) (hlek b.1) (A (ix b.1))
    C := fun b => trC (hkM b.1) (hlek b.1) (C (ix b.1))
    CA := fun b => trC_mul_trA _ _ _ _ (hCA _)
    tw := fun S _ x b b' h h' hM => tw_tr (hkM b.1) (hkM b'.1) (hlek b.1) (hlek b'.1) (hUM _ _) (A (ix b.1))
      (A (ix b'.1)) (L.g (ix b.1) (ix b'.1)) (fun K _ w hw hw' => htw K w _ _ hw hw') S x h h' hM }⟩

theorem exists_cellModel (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) :
    ∃ (M : FlagModel Y) (g : ∀ en : En Dw.mult, M.YY ⟶ PSpace c.F (plN A.N en.1))
      (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ M.YY)) (_ : ∀ b w, IsOpenImmersion (κ b w)),
      Cells A M.π g κ := by
  have := A.fin
  obtain ⟨Z, π, g, κ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_proper_normal_flagScheme_of_affine_cover c.F Y.X Y.s (E →+* ℂ) Dw.mult A.N A.B A.V A.alpha A.cv
    A.Dv Y.proj Y.normal (GlobalTheory.T.eigenbundleFrameAffineAtlas_isFlagFrameCover E H Dw l Xo c Y p A) A.cov
  have hZ : Cells A π g κ := ⟨h1, h2, h3, h5, h6⟩
  have := h4
  have ht := GlobalTheory.T.flagCellFrameChangeTriangular_of_cells E H Dw l Xo c Y p A Z π g κ hZ
  have huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z),
      (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂ := by
    intro S' _ _ P₁ z₁ z₂ e₁ e₂
    refine GlobalTheory.T.spec_hom_ext_of_localizations_at_all_primes S' Z z₁ z₂ fun q => ?_
    obtain ⟨P', hP'⟩ := exists_frMap (IsScalarTower.toAlgHom c.F S' (Localization.AtPrime q.asIdeal)) P₁
    have l₁ := e₁.frMap hP'
    have l₂ := e₂.frMap hP'
    refine GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing E H Dw l Xo c Y p A Z π g κ hZ ht _ _ _ _ l₁.1 l₂.1 fun σ i => ?_
    obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover
      (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₁)
    obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover
      (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₂)
    exact (l₁.initSpan_eq hk l₁.1 rfl σ i).symm.trans (l₂.initSpan_eq hk' l₂.1 rfl σ i)
  refine ⟨{ YY := Z, π := π, proper := h1, normal := h2, flat := ?_, F := cellFrames hZ ht
            dense := GlobalTheory.T.dense_flagBundle_preimage_moduli E H Dw l Xo c Y p A Z π g κ hZ, top := GlobalTheory.T.flagCellFrames_lastStep_eigenmodules E H Dw l Xo c Y p A Z π g κ hZ ht
            rep := fun S _ _ P => ?_, fin := fun K _ _ z => ?_ }, g, κ, h4, hZ⟩
  · exact GlobalTheory.T.flat_to_spec_field' c.F Z (π ≫ Y.s)
  · obtain ⟨z, hz⟩ := GlobalTheory.T.exists_flagBundle_point_carrying_of_local E H Dw l Xo c Y p A Z π g κ hZ ht S P huniq fun q =>
      GlobalTheory.T.exists_flagCell_containing_framed_point E H Dw l Xo c Y p A Z π g κ hZ ht S P q
    exact ⟨z, hz, fun z' hz' => huniq S P z' z hz' hz⟩
  · refine (Set.finite_singleton z).subset fun z' ⟨hx, h⟩ => ?_
    exact GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing E H Dw l Xo c Y p A Z π g κ hZ ht K z' z _ hx rfl h

theorem smooth_proj_flagStr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (T : GlobalTheory.CompHS.TorFlag Xo c), ∃ d : ℕ, SmoothOfRelativeDimension d (GlobalTheory.CompHS.flagStr T.X) ∧ IsProjOver (GlobalTheory.CompHS.flagStr T.X) := by
  intro E _ _ _ H D l Xo c T
  obtain ⟨p⟩ := GlobalTheory.FlagMod.LowRank.nonempty_proj_id (E := E) (c := c)
  obtain ⟨A⟩ := nonempty_atlas_of_cover T.Y p (exists_gChart_of_flagCover T.X)
  obtain ⟨M, g, κ, hκ, hZ⟩ := exists_cellModel T.Y p A
  obtain ⟨d, hsm, hpr⟩ := GlobalTheory.T.flag_atlas_projective_embedding E H D l Xo c T.Y p A M.YY M.π g κ hκ hZ T.smooth
  obtain ⟨h, hh, hπ⟩ := GlobalTheory.T.exists_flagModel_isIso_of_open_cells E H D l Xo c T.Y p A M g κ hκ hZ T.smooth T.flag
  have e : flagStr T.X = h ≫ M.π ≫ T.Y.s := by
    rw [← Category.assoc, hπ]
  refine ⟨d, ?_, ?_⟩
  · rw [e]; exact GlobalTheory.VarFlag.smooth_iso h _ hsm
  · rw [e]
    obtain ⟨N, i, hi, hs⟩ := hpr
    exact ⟨N, h ≫ i, inferInstance, by rw [Category.assoc, hs]⟩

end GlobalTheory.CompanionTheory.FlagSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagOnHodgeOfFargues
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
namespace GlobalTheory.CompanionTheory.Ar.Num

def zpLocSubalg (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] : Subalgebra ℤ Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      · exact hb h
      · exact hb' h
    · push_cast
      rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb (h ▸ dvd_zero p))
    have hb0' : (b' : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb' (h ▸ dvd_zero p))
    refine ⟨a * b' + b * a', b * b', fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      · exact hb h
      · exact hb' h
    · rw [div_add_div _ _ hb0 hb0']
      push_cast
      ring
  algebraMap_mem' := by
    intro a
    refine ⟨a, 1, fun h => (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h), ?_⟩
    simp

theorem mem_range_zpLocSubalg (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] (x : Ω) :
    x ∈ (algebraMap (zpLocSubalg Ω p) Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mem_chartRing_of_range_le {o o' : Type} [CommRing o] [CommRing o'] {Ω : Type} [Field Ω] [Algebra o Ω]
    [Algebra o' Ω] (hr : ∀ a : o, algebraMap o Ω a ∈ (algebraMap o' Ω).range) {ι' : Type} (z : ι' → Ω) (s : ι')
    {w : Ω} (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing o z s) : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing o' z s := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.chartRing at *
  induction hw using Algebra.adjoin_induction with
  | mem w hw => exact Algebra.subset_adjoin hw
  | algebraMap r =>
    obtain ⟨a, ha⟩ := hr r
    rw [← ha]
    exact Subalgebra.algebraMap_mem _ a
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem trivFlagMod_of_range_le {o o' : Type} [CommRing o] [CommRing o'] {Ω : Type} [Field Ω] [Algebra o Ω]
    [Algebra o' Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (hr : ∀ a : o, algebraMap o Ω a ∈ (algebraMap o' Ω).range) (ϖ : o) (ϖ' : o')
    (hϖ : algebraMap o' Ω ϖ' = algebraMap o Ω ϖ) (x : (Σ k, ι k) → Ω) (N : ℕ) (b : Fin N → K → ℤ)
    (h : TrivFlagMod o ϖ x N b) : TrivFlagMod o' ϖ' x N b := by
  obtain ⟨g, h1, h2⟩ := h
  refine ⟨g, fun s hs => ?_, fun s t hs ht => ?_⟩
  · obtain ⟨hg, e, he, r, hr', heq⟩ := h1 s hs
    exact ⟨fun i j => mem_chartRing_of_range_le hr _ _ (hg i j), e, mem_chartRing_of_range_le hr _ _ he, r,
      mem_chartRing_of_range_le hr _ _ hr', by rw [hϖ]; exact heq⟩
  · obtain ⟨m, U, Z, hU, hZ, hlow, hdiag, hgs, heq⟩ := h2 s t hs ht
    exact ⟨m, U, Z, fun i j => mem_chartRing_of_range_le hr _ _ (hU i j),
      fun i j => mem_chartRing_of_range_le hr _ _ (hZ i j), hlow, hdiag,
      fun i j => mem_chartRing_of_range_le hr _ _ (hgs i j), by rw [hϖ]; exact heq⟩

theorem trivFlagMod_of_eq_zero (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (ϖ : o) (x : (Σ k, ι k) → Ω) (N : ℕ) (hN : N = 0) (b : Fin N → K → ℤ) :
    TrivFlagMod o ϖ x N b := by
  subst hN
  refine ⟨fun _ => 0, fun s _ => ⟨fun i => i.elim0, 1, one_mem _, 0, zero_mem _, by simp⟩,
    fun s t _ _ => ⟨0, 0, 0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, Subsingleton.elim _ _⟩⟩

theorem isUnit_natCast_of_not_dvd {A O : Type} [CommRing A] [CommRing O] [IsLocalRing O] [Algebra A O]
    (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime O m] (p : ℕ) [Fact p.Prime] (hpm : (p : A) ∈ m) (b : ℕ)
    (hb : ¬ p ∣ b) : IsUnit (b : O) := by
  by_contra hu
  have hbO : algebraMap A O (b : A) ∈ IsLocalRing.maximalIdeal O := by
    rw [map_natCast]
    exact hu
  have hbm : (b : A) ∈ m := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m _).1 hbO
  have hcop : IsCoprime (b : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hb).symm
  obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom A)
  have h1 : (1 : A) ∈ m := by
    rw [← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact add_mem (m.mul_mem_left _ hbm) (m.mul_mem_left _ hpm)
  exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h1)

theorem trivFlagOnHodge_of_fargues : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → TrivFlagOnHodge := by
  intro hF
  unfold TrivFlagOnHodge
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd Fl x e hRL p hpS hHT A _ _ _
  unfold AtPlacesOver
  intro m _ hpm O _ _ _ _ _ _ _ τ W hW
  haveI : Fact p.Prime := ⟨𝔐.S_prime p hpS⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hflag : TrivFlagMod O ϖ y (D.p + D.q) (fun i => x (τ, i)) := by
    rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
    · exact trivFlagMod_of_eq_zero O ϖ y _ h0 _
    · have hint := intCast_injective_of_isArithVar hd
      haveI : CharZero Ω := ⟨fun a b hab => by
        have : Int.castRingHom Ω (a : ℤ) = Int.castRingHom Ω (b : ℤ) := by simpa using hab
        exact_mod_cast hint this⟩
      have h1 := GlobalTheory.T.hodge_tate_free_trivial_flag_mod hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hpos (zpLocSubalg Ω p)
        (mem_range_zpLocSubalg Ω p) Fl x e hHT hRL τ
      have hr : ∀ a : zpLocSubalg Ω p, algebraMap (zpLocSubalg Ω p) Ω a ∈ (algebraMap O Ω).range := by
        intro a
        obtain ⟨a₁, b, hb, hab⟩ := (mem_range_zpLocSubalg Ω p _).1 ⟨a, rfl⟩
        have hu := isUnit_natCast_of_not_dvd (O := O) m p hpm b hb
        refine ⟨(a₁ : O) * ↑hu.unit⁻¹, ?_⟩
        rw [hab, map_mul, map_intCast, div_eq_mul_inv]
        congr 1
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← map_natCast (algebraMap O Ω) b, ← map_mul, hu.val_inv_mul, map_one]
      have h2 : TrivFlagMod O ((p : O) ^ (𝔐.R p - 2)) y (D.p + D.q) (fun i => x (τ, i)) :=
        trivFlagMod_of_range_le hr _ _ (by simp) _ _ _ h1
      have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O := by
        have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hpm
        rwa [map_natCast] at this
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hpO
      have hR : 𝔐.R p - 2 ≠ 0 := by
        have := 𝔐.R_ge p hpS
        omega
      exact GlobalTheory.T.triv_flag_mod_of_dvd O Ω K J y _ ϖ _ _ (dvd_pow hpO hR) h2
  have hJ := isMultiHomogIdeal_pointIdeal_sup_map_C (ι := J) (O := O) y (IsLocalRing.maximalIdeal O)
  have hWh := GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof.{0} O K J _ W hJ hW.1
  have hCϖ : (C ϖ : GroundTheory.Heights₂.Heights.NumbersDVR.MRing J O) ∈ W :=
    hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _
      ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)))
  exact GlobalTheory.T.trivial_flag_at_prime O Ω K J y ϖ hϖ _ _ hflag W ⟨hW.1.1.1, hWh, hW.2⟩ (le_sup_left.trans hW.1.1.2) hCϖ

end GlobalTheory.CompanionTheory.Ar.Num
end

