import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open TopologicalSpace
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.SharedLaws

section Top

variable {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

theorem exists_finite_generic {F : Set X} (hF : IsClosed F) :
    ∃ G : Set X, G.Finite ∧ G ⊆ F ∧ ∀ x ∈ F, ∃ g ∈ G, g ⤳ x := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  choose η hη using fun t (ht : t ∈ S) => QuasiSober.sober (hi t ht) (hc t ht)
  haveI := hS.to_subtype
  refine ⟨Set.range fun t : S => η t.1 t.2, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨t.1, t.2, (hη t.1 t.2).mem⟩
  · rintro x ⟨t, ht, hx⟩
    exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, (hη t ht).specializes hx⟩

theorem finite_maximal {F : Set X} (hF : IsClosed F) :
    Finite {x : X // x ∈ F ∧ ∀ x' : X, x' ∈ F → x' ⤳ x → x' = x} := by
  obtain ⟨G, hG, hGF, h⟩ := exists_finite_generic hF
  refine (hG.subset (s := G) (t := {x | x ∈ F ∧ ∀ x' : X, x' ∈ F → x' ⤳ x → x' = x}) ?_).to_subtype
  rintro x ⟨hx, hm⟩
  obtain ⟨g, hg, hgx⟩ := h x hx
  exact hm g (hGF hg) hgx ▸ hg

theorem nonempty_maximal [T0Space X] {F : Set X} (hF : IsClosed F) (hne : F.Nonempty) :
    Nonempty {x : X // x ∈ F ∧ ∀ x' : X, x' ∈ F → x' ⤳ x → x' = x} := by
  obtain ⟨G, hG, hGF, h⟩ := exists_finite_generic hF
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g₀, hg₀, -⟩ := h x hx
  obtain ⟨g, hg⟩ := hG.exists_maximalFor (fun g : X => closure ({g} : Set X)) G ⟨g₀, hg₀⟩
  refine ⟨⟨g, hGF hg.1, fun x' hx' hs => ?_⟩⟩
  obtain ⟨g', hg', hs'⟩ := h x' hx'
  have h1 := hg.2 hg' (specializes_iff_closure_subset.1 (hs'.trans hs))
  exact (hs.antisymm ((specializes_iff_closure_subset.2 h1).trans hs')).eq

theorem mem_of_maximal {x : X} (hx : ∀ x' : X, x' ⤳ x → x' = x) {U : Set X} (hU : IsOpen U) (hd : Dense U) :
    x ∈ U := by
  obtain ⟨G, hG, -, h⟩ := exists_finite_generic (isClosed_univ (X := X))
  have hC : IsClosed (⋃ g ∈ G \ {x}, closure ({g} : Set X)) :=
    (hG.subset Set.diff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  obtain ⟨y, hy, hyU⟩ := hd.inter_open_nonempty _ hC.isOpen_compl ⟨x, fun hm => by
    obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 hm
    exact hg.2 (hx g (specializes_iff_mem_closure.2 hgx))⟩
  obtain ⟨g, hg, hgy⟩ := h y trivial
  by_cases e : g = x
  · exact (e ▸ hgy).mem_open hU hyU
  · exact absurd (Set.mem_iUnion₂.2 ⟨g, ⟨hg, e⟩, specializes_iff_mem_closure.1 hgy⟩) hy

end Top

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_nonunits_V {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem isProper_toroidalModel_structureMap (Z : Mdl Y i₀) : IsProper Z.s := by
  have := isProper_str (Z.i.c.V W) Z.n
  unfold Pre.s
  infer_instance

theorem noetherianSpace (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : NoetherianSpace Z.X := by
  haveI := Z.i.c.fin
  haveI : NumberField Z.i.c.F := {}
  haveI := (isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp
    (mem_nonunits_V Z.i.c hp hW)).1
  haveI := isProper_toroidalModel_structureMap Z
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  haveI : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  haveI : IsNoetherian Z.X := {}
  infer_instance

theorem nonempty_model (h1 : 1 ≤ Dw.p + Dw.q) (Z : Mdl Y i₀) : Nonempty Z.X := by
  obtain ⟨⟨C⟩, -, h, -⟩ := GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg E H Dw Z.i.l (Xo Z.i.l) Z.i.c h1
  obtain ⟨P, -⟩ := h C
  obtain ⟨g, -⟩ := Descent.exists_tie_frame (Z := Y Z.i) P rfl
  obtain ⟨w, -⟩ := Z.bij _ _ _ (Descent.ptF_snd P) g.v ⟨fun τ i => ⟨g.tan τ i, g.eig τ i⟩, g.basis⟩
  exact ⟨w (IsLocalRing.closedPoint _)⟩

theorem not_inQ_iff (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (x : Z.X) :
    ¬ Z.inQ x ↔ (p : Z.X.residueField x) = 0 := by
  constructor
  · intro h
    by_contra hne
    apply h
    let φ : Z.i.c.V W →+* Z.X.residueField x :=
      (Z.X.evaluation ⊤ x trivial).hom.comp (GlobalTheory.QCoh.structureRingHom Z.s)
    obtain ⟨q, hq⟩ := CharP.exists (Z.X.residueField x)
    rcases CharP.char_is_prime_or_zero (Z.X.residueField x) q with hqp | rfl
    · exfalso
      have hpq : p ≠ q := by
        rintro rfl
        exact hne (CharP.cast_eq_zero _ _)
      have hco : IsCoprime (p : Z.i.c.V W) (q : Z.i.c.V W) := by
        exact_mod_cast (Nat.Coprime.cast (R := Z.i.c.V W) ((Nat.coprime_primes hp hqp).2 hpq))
      have hpn : ¬ IsUnit (p : Z.i.c.V W) := by
        have := mem_nonunits_V Z.i.c hp.ne_zero hW
        have h2 := (ValuationSubring.coe_mem_nonunits_iff (A := Z.i.c.V W) (a := (p : Z.i.c.V W))).1 (by simpa using this)
        exact h2
      obtain ⟨a, b, hab⟩ := hco
      have hqu : IsUnit (q : Z.i.c.V W) := by
        rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
        · exact absurd (isUnit_of_mul_isUnit_right h) hpn
        · exact isUnit_of_mul_isUnit_right h
      have := hqu.map φ
      rw [map_natCast, CharP.cast_eq_zero] at this
      exact not_isUnit_zero this
    · exact CharP.charP_to_charZero _
  · intro h hc
    haveI : CharZero (Z.X.residueField x) := hc
    exact hp.ne_zero (by exact_mod_cast h)

theorem setOf_not_inQ (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) :
    {x : Z.X | ¬ Z.inQ x} = (Z.genO : Set Z.X)ᶜ := by
  ext x
  rw [Set.mem_setOf_eq, not_inQ_iff hp hW, ← map_natCast (Z.X.evaluation ⊤ x trivial).hom]
  exact Scheme.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) Z.X x trivial _

theorem nonempty_special (h1 : 1 ≤ Dw.p + Dw.q) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) :
    ((Z.genO : Set Z.X)ᶜ).Nonempty := by
  haveI := isProper_toroidalModel_structureMap Z
  obtain ⟨x⟩ := nonempty_model h1 Z
  have hc : IsClosed (Set.range Z.s) := Z.s.isClosedMap.isClosed_range
  obtain ⟨y, hy⟩ : IsLocalRing.closedPoint (Z.i.c.V W) ∈ Set.range Z.s :=
    (IsLocalRing.specializes_closedPoint (Z.s x)).mem_closed hc ⟨x, rfl⟩
  refine ⟨y, fun hm => ?_⟩
  have e : Z.genO = Z.s ⁻¹ᵁ (Sp (Z.i.c.V W)).basicOpen ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv (p : Z.i.c.V W)) := by
    rw [Scheme.preimage_basicOpen_top, map_natCast, map_natCast]
    rfl
  rw [e, basicOpen_eq_of_affine] at hm
  have hm' : Z.s y ∈ PrimeSpectrum.basicOpen (p : Z.i.c.V W) := hm
  rw [hy] at hm'
  exact hm' ((ValuationSubring.coe_mem_nonunits_iff (A := Z.i.c.V W) (a := (p : Z.i.c.V W))).1
    (by simpa using mem_nonunits_V Z.i.c hp.ne_zero hW))

theorem abP_of_isGenP (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (x : Z.X) (hx : Z.isGenP x) :
    Z.abP x := by
  haveI := noetherianSpace hp hW Z
  have ho : IsOpen Z.opn := by
    rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.2
  obtain ⟨z, hz⟩ := mem_of_maximal hx ho Z.dense
  have : (Y Z.i).jQ z ∈ pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype) ⁻¹' abLocus (Y Z.i).t.G := by
    rw [(Y Z.i).ab_gen]
    exact ⟨z, rfl⟩
  unfold Mdl.abP
  rw [← hz]
  exact this

theorem isFiniteQC_toMod (Z : Mdl Y i₀) (F : Z.Sh) : GlobalTheory.QCoh.IsFiniteQC F.toMod := by
  have h : ∀ a m, GlobalTheory.QCoh.IsFiniteQC (Z.free a m) := fun a m =>
    GlobalTheory.Twist.isFiniteQC_twist (LB.isLB_pull (GlobalTheory.ProjSpace.On_isLB _ _ _) _)
  haveI := h F.a F.m
  haveI := h F.a' F.m'
  exact GlobalTheory.QCoh.isFiniteQC_cokernel F.φ

theorem nrm_nonneg (Z : Mdl Y i₀) (F : Z.X.Modules) (f : Γ(F, Z.genO)) (y : Z.Pt) : 0 ≤ Mdl.nrm F f y :=
  Real.sSup_nonneg (by
    rintro r ⟨U, -, h, k, g, lam, -, rfl⟩
    positivity)

theorem nrm_le_one (hp : p ≠ 0) (Z : Mdl Y i₀) (F : Z.X.Modules) [F.IsQuasicoherent] (g₀ : Γ(F, ⊤)) (y : Z.Pt) :
    Mdl.nrm F ((F.presheaf.map (homOfLE (le_top : Z.genO ≤ ⊤)).op).hom g₀) y ≤ 1 := by
  refine Real.sSup_le ?_ zero_le_one
  rintro r ⟨U, hU, h, k, g, lam, hg, rfl⟩
  set g₁ : Γ(F, U) := (F.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom g₀ with hg₁
  have e : U ⊓ Z.genO = Z.X.basicOpen ((p : ℕ) : Γ(Z.X, U)) := by
    rw [← map_natCast (Z.X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom, Scheme.basicOpen_res]
    rfl
  obtain ⟨n, hn⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_zero F hU _ inf_le_left e (g - p ^ k • g₁) (by
    rw [map_sub, map_nsmul, sub_eq_zero]
    refine hg.trans (congrArg _ ?_)
    rw [hg₁]
    change (F.presheaf.map _ ≫ F.presheaf.map _).hom g₀ = (F.presheaf.map _ ≫ F.presheaf.map _).hom g₀
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl)
  have h2 := congrArg lam hn
  rw [map_smulₛₗ, map_zero, map_sub, map_nsmul, map_pow, map_natCast, smul_eq_mul] at h2
  have hp' : ((p : ↥(intO ↥y.C.S))) ≠ 0 := Nat.cast_ne_zero.2 hp
  have h3 : lam g = p ^ k • lam g₁ := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ hp'))
  have h4 : ‖((lam g₁ : ↥(intO ↥y.C.S)) : ↥y.C.S)‖ ≤ 1 := (lam g₁).2
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [h3, nsmul_eq_mul]
  push_cast
  rw [norm_mul, norm_pow, y.C.norm_p, mul_right_comm, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]
  exact h4

end Free

theorem lawSt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ), ∀ ct : At S κ p, LawSt ct := by
  intro D A N j S κ p ct
  have h1 : 1 ≤ S.Dw.p + S.Dw.q := by have := S.rank_eq; have := S.two_le; omega
  refine ⟨fun F f y => nrm_nonneg _ _ f y, ?_, fun l => ?_, fun x hx => abP_of_isGenP ct.hp.ne_zero ct.hW _ x hx,
    fun Z => ?_, fun Z => ?_, ?_⟩
  · rintro Z F f ⟨g₀, rfl⟩ y
    haveI := isFiniteQC_toMod Z F
    exact nrm_le_one ct.hp.ne_zero Z F.toMod g₀ y
  · have h := GlobalTheory.T.graded_line_bundle_exists _ _ _ _ p ct.W ct.hp ct.hW _ _ ct.YY ct.isYY.2.1 (ct.expo l)
    have hv := GlobalTheory.VB.isVB_toMod h.choose_spec.1
    haveI := hv.isFiniteQC
    obtain ⟨e⟩ := GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso _ _ _ _ p ct.W ct.hp ct.hW _ _ ct.YY (GlobalTheory.LB.toMod h.choose)
    unfold At.IsInv At.Lb
    rw [dif_pos h]
    exact hv.of_iso e.symm
  · haveI := noetherianSpace ct.hp.ne_zero ct.hW Z
    exact finite_maximal (F := {x : Z.X | ¬ Z.inQ x}) (by
      rw [setOf_not_inQ ct.hp ct.hW]; exact Z.genO.2.isClosed_compl)
  · haveI := noetherianSpace ct.hp.ne_zero ct.hW Z
    exact nonempty_maximal (F := {x : Z.X | ¬ Z.inQ x}) (by
      rw [setOf_not_inQ ct.hp ct.hW]; exact Z.genO.2.isClosed_compl) (by
      rw [setOf_not_inQ ct.hp ct.hW]; exact nonempty_special h1 ct.hp ct.hW Z)
  · intro Z y c c' hc a
    have e : c' = A.H.bar c := by
      apply RingOfIntegers.ext
      rw [hc, A.H.bar_eq]
      apply D.host.φ₀.injective
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    subst e
    rfl

end GlobalTheory.LocM.SharedLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReps
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ArcExt

open MonoidalCategory CartesianMonoidalCategory

def LevelRep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (y : Sp V ⟶ Y.X) (t : SAB H (Sp V)) (m : SABMap t Y.t y)
    (P : PELUnif (maximalIdeal V) t) (k : ℕ) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Prop :=
  ∃ r : Out.QkPt P.D.toPre (FractionRing V) k,
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (yF : Sp F ⟶ Xo.XF c),
      yF ≫ Y.j = Out.jFK (R := V) F ≫ Out.jK V ≫ y →
      ∀ (q : Out.QkPt P.D.toPre F k) (x : Out.TFK (R := V) F ⟶ P.A.A), QkExt (algebraMap _ F) r q →
        x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK V) ≫ m.φ = yF ≫ σ.left ≫ Y.m.φ →
        P.ToA F k q x

def LevelReps {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (y : Sp V ⟶ Y.X) (t : SAB H (Sp V)) (m : SABMap t Y.t y)
    (P : PELUnif (maximalIdeal V) t) : Prop :=
  (∀ v, LevelRep Y y t m P l.A (Y.oF.etaA v)) ∧
    ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), LevelRep Y y t m P l.M (Y.oF.eta v)

end GlobalTheory.ArcExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogGramSquareSmooth
section
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder

set_option autoImplicit false

open scoped ContDiff

namespace GlobalTheory

theorem smoothOn_log_grSq : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)) (M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → (∀ y ∈ S, (M y).PosDef) → ∀ i : Fin m, R.SmoothOn S (fun y => Real.log (grSq (M y) i)) := by
  intro k _ Y p σ D m R S M hM hP i j
  have hE : ∀ a b, ContDiffOn ℝ ∞ (fun v => M ((R.chart j).e.symm v) a b)
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' S) := fun a b => by
    have h1 := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hM a b).1 j)
    have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hM a b).2 j)
    refine (h1.add (h2.mul (contDiffOn_const (c := Complex.I)))).congr fun v _ => ?_
    simp [Function.comp_def, Complex.re_add_im]
  have hL : ∀ K : Fin (m + 1), ContDiffOn ℝ ∞ (fun v => ReciprocityTheory.ChartRestriction.G.FD.lminor (M ((R.chart j).e.symm v)) K)
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' S) := fun K => by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.lminor, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    exact ContDiffOn.sum fun π _ => contDiffOn_const.mul (contDiffOn_prod fun c _ => hE _ _)
  have hq := (hL i.succ).mul ((hL i.castSucc).inv fun v (hv : v ∈ (R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' S) =>
    (GlobalTheory.GradedNorm.lminor_pos (hP _ hv.2) _).ne')
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hq
  exact (hr.log fun v hv => (grSq_pos (hP _ hv.2) i).ne').congr fun v _ => by simp [grSq, div_eq_mul_inv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendsto
section
open GlobalTheory.ShFam.BdArc Filter Topology

namespace GlobalTheory.ShFam.BdArc

theorem exists_complexPoint_of_notMem {F A : Type} [Field F] [CommRing A] [Algebra F A] [Algebra.FiniteType F A]
    (σ : F →+* ℂ) (P : Ideal A) [hP : P.IsPrime] {s : A} (hs : s ∉ P) :
    ∃ ψ : A →+* ℂ, ψ.comp (algebraMap F A) = σ ∧ (∀ x ∈ P, ψ x = 0) ∧ ψ s ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := F)
  have hj : P.jacobson = P := IsJacobsonRing.out inferInstance hP.isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf] at hs
  push Not at hs
  obtain ⟨M, ⟨hle, hM⟩, hsM⟩ := hs
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite F (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ M)
  let _ : Algebra F ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[F] ℂ := IsAlgClosed.lift
  refine ⟨(κ.comp (Ideal.Quotient.mkₐ F M)).toRingHom, ?_, fun x hx => ?_, ?_⟩
  · ext x
    exact (κ.comp (Ideal.Quotient.mkₐ F M)).commutes x
  · show κ (Ideal.Quotient.mk M x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]
  · show κ (Ideal.Quotient.mk M s) ≠ 0
    rw [map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hsM

theorem dvd_or_dvd_of_height_eq_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (a b : A) :
    (∃ s, s ∉ P ∧ a ∣ s * b) ∨ ∃ s, s ∉ P ∧ b ∣ s * a := by
  have := GlobalTheory.isDiscreteValuationRing_of_height_eq_one P hP (Localization.AtPrime P)
  have key : ∀ x y : A, algebraMap A (Localization.AtPrime P) x ∣ algebraMap A _ y → ∃ s, s ∉ P ∧ x ∣ s * y := by
    rintro x y ⟨c, hc⟩
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨d, d.2, n, ?_⟩
    apply IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
    simp only at hnd
    rw [map_mul, map_mul, hc, ← hnd]
    ring
  exact (ValuationRing.dvd_total (algebraMap A (Localization.AtPrime P) a) (algebraMap A _ b)).imp (key a b) (key b a)

theorem exists_eq_mul_pow_of_tendsto_zero : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (σ : F →+* ℂ) (p a : A) (m : ℕ), p ≠ 0 → (∀ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = σ) → ψ 0 p = 0 → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0) → Tendsto (fun u => ψ u a / ψ u (p ^ m)) (𝓝[≠] 0) (𝓝 0)) → ∃ b : A, a = b * p ^ m ∧ b ∈ (Ideal.span {p}).radical := by
  intro F A _ _ _ _ hsm σ p a m hp h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth F A
  have key : ∀ (P : Ideal A) [P.IsPrime], p ∈ P → ∀ s, s ∉ P → ¬ a ∣ s * p ^ m := by
    rintro P _ hpP s hs ⟨t, ht⟩
    obtain ⟨ψ₀, hσ, hP0, hs0⟩ := exists_complexPoint_of_notMem σ P hs
    obtain ⟨ψ, r, hhol, h0, hσ', hne⟩ := GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing F A hsm ψ₀ p hp
    have hlim := h ψ r hhol (fun u hu => (hσ' u hu).trans hσ) (by rw [h0]; exact hP0 p hpP) hne
    have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hhol.1
    have hc : ∀ x, Tendsto (fun u => ψ u x) (𝓝[≠] 0) (𝓝 (ψ₀ x)) := fun x => by
      rw [← h0]
      exact (((hhol.2 x).differentiableAt hball).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h1 := hlim.mul (hc t)
    rw [zero_mul] at h1
    have h2 : Tendsto (fun u => ψ u s) (𝓝[≠] 0) (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
      have hpu : ψ u (p ^ m) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (hne u hu hu0)
      rw [div_mul_eq_mul_div, ← map_mul, ← ht, map_mul, mul_div_cancel_right₀ _ hpu]
    exact hs0 (tendsto_nhds_unique (hc s) h2)
  obtain ⟨b, hb⟩ : p ^ m ∣ a := by
    refine GlobalTheory.dvd_of_forall_height_eq_one (pow_ne_zero m hp) fun P hP h1 hpm => ?_
    refine (dvd_or_dvd_of_height_eq_one P h1 (p ^ m) a).resolve_right ?_
    rintro ⟨s, hs, hd⟩
    exact key P (hP.mem_of_pow_mem m hpm) s hs hd
  refine ⟨b, by rw [hb, mul_comm], ?_⟩
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hle, hP⟩
  by_contra hbP
  exact key P (hle (Ideal.mem_span_singleton_self p)) b hbP ⟨1, by rw [hb]; ring⟩

end GlobalTheory.ShFam.BdArc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportional
section
noncomputable section

namespace GlobalTheory.FlagEmb

theorem adjugate_mul_eq_plk {K : Type} [Field K] {M k : ℕ} (D : Fin k → Fin (M + 1) → K) (r : Fin k → Fin (M + 1))
    (i : Fin k) (s : Fin (M + 1)) :
    ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      plk D id ((plE M k).symm (Function.update r i s)) := by
  have h1 : ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      ((Matrix.of fun l l' => D l (r l')).adjugate.mulVec fun j => D j s) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  simp only [plk, Equiv.apply_symm_apply, id]
  congr 1
  ext l l'
  by_cases h : l' = i
  · subst h
    simp [Matrix.updateCol_apply]
  · simp [Matrix.updateCol_apply, Function.update_of_ne h, h]

theorem mem_span_of_plk_eq_smul (K : Type) [Field K] (M k : ℕ) (c c' : Fin k → Fin (M + 1) → K) (a : K)
    (h0 : plk c' id ≠ 0) (h : plk c' id = a • plk c id) (l : Fin k) :
    c' l ∈ Submodule.span K (Set.range c) := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h0
  set r := plE M k q with hr
  set A : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c l (r l') with hA
  set A' : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c' l (r l') with hA'
  have hdet : A'.det ≠ 0 := hq
  have hadj : A'.adjugate * Matrix.of c' = a • (A.adjugate * Matrix.of c) := by
    ext i s
    rw [hA, hA', adjugate_mul_eq_plk, Matrix.smul_apply, adjugate_mul_eq_plk, h]
    rfl
  have hC : A'.det • (Matrix.of c' : Matrix (Fin k) (Fin (M + 1)) K) = a • (A' * A.adjugate * Matrix.of c) := by
    have := congrArg (fun X => A' * X) hadj
    simp only [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul] at this
    simpa [Matrix.smul_mul] using this
  have hrow : c' l = ∑ j, ((A'.det)⁻¹ * (a * (A' * A.adjugate) l j)) • c j := by
    funext s
    have h2 := congrFun (congrFun hC l) s
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.mul_apply (M := A' * A.adjugate)] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [eq_inv_mul_iff_mul_eq₀ hdet |>.2 h2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrow]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.FlagEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStOneOfInt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftBrg.StdFrame

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end

theorem castGL_rfl {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : castGL (rfl : m = m) x = x := by
  ext i j
  simp [castGL]

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end

theorem isSplitSet_sgL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (hI : I.Ok) (t : TupU I U) :
    Formalism.L2.DIV.IsSplitSet (sgL X I U t) := by
  have hX := (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).1
  have hPr := (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).2.1
  intro P1 h1 P2 h2 h12
  have := GlobalTheory.LevMuDet.conjP_notMem_rowSG t.1 hX hPr hI.sel_ok hI.g_mem h1
  apply this
  have e : Formalism.L2.Col.conjPrime₂ P1 = P2 := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    ext r
    rw [Formalism.L2.Col.mem_conjP]
    refine h12 _ r ?_
    show (r : X.toD7.host.E) = star (star (r : X.toD7.host.E))
    rw [star_star]
  subst e; exact h2

end GlobalTheory.Mem.R3.LiftBrg.StdFrame

namespace GlobalTheory.Mem.R3.LiftBrg

end GlobalTheory.Mem.R3.LiftBrg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowMemArithmeticSubgroupOfStabilizerStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mem_arithmetic_subgroup_of_stabilizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (g : GL (Fin N) E), IsUStab X.Gm X.Λ g → ∃ k : ℕ, 0 < k ∧ g ^ k ∈ X.Γ := by
  first | exact @GlobalTheory.UnipKill.pow_mem_of_isUStab | exact GlobalTheory.UnipKill.pow_mem_of_isUStab | (intros; apply GlobalTheory.UnipKill.pow_mem_of_isUStab <;> assumption)
end

