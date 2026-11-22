import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3339
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0194
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3335

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalkCompat
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatValZero

section Gen

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem nonempty_keySec (hL : Laws U x) : Nonempty (KeySec Xo c) := by
  obtain ⟨κ, k₁, k₂, -, k₄, -, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨ρ, -⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0) hL.geo hL.pos
    hKmem hKval
  exact ⟨ρ⟩

def unitsV (T : CDVR) : Submonoid T.Fr where
  carrier := {z | z ≠ 0 ∧ vV T.V z = 0}
  one_mem' := ⟨one_ne_zero, by simp [vV]⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by rw [vV_mul ha.1 hb.1, ha.2, hb.2, add_zero]⟩

theorem twSec_flat_val (hP : GlobalTheory.CovTop.Hypotheses2) (hL : Laws U x) (hFE : FlatExists U x) (Z : Comp Xo c)
    (w : Psi H → ℤ) : ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0), ∀ (T : CDVR) (io : c.F →+* T.Fr)
      (y : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → evI y (idem Z) ≠ 0 → vV T.V (evI y t.sig) = 0 := by
  have hp : HasPts U Z := GlobalTheory.FlatLine.hasPts U hL.pos hL.good hL.unf Z
  let sF : ∀ τ, FlatSec U x Z τ := fun τ => (hFE.nonempty Z τ).some
  have hK := nonempty_keySec hL
  let s := FlatSec.shift hp sF w
  have hδ := GlobalTheory.FlatTwisting.finite_sum_flDefect (Dw := Dw) (c := c) w
  refine ⟨TwSec.ofConst s (by convert hδ) (GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos s) fun G hG f hf => ?_,
    fun T io y hio hZ => ?_⟩
  · have h := GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos (w := -w) (s.symm.copy rfl rfl)
      (G + wtOf Dw (parWt Dw w) 0) (Even.add hG (even_wtOf _ _)) f hf
    rw [GlobalTheory.FlatTwisting.wtOf_parWt_neg, add_neg_cancel_right] at h
    exact h
  letI := io.toAlgebra
  have hLies : LiesOn Z y.1 := by
    by_contra hn
    exact hZ ((idem_mem_suppOn Z) T.Fr y.1 ((liesOff_iff Z y.1).2 hn))
  have hid : evI y (idem Z) = 1 := by
    have e := evI_mul y (idem Z) (idem Z)
    rw [idem_mul_idem] at e
    exact mul_left_cancel₀ hZ (by rw [mul_one]; exact e.symm)
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hsig : ∀ τ, ev (sF τ).sig ∈ unitsV T := fun τ => by
    have hn := GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero hP hP.q2 hP.q3 E H Dw l Xo c r U x hL Z τ
      (ArchSec.ofConst (sF τ)) T io y hio hLies
    have hev0 : evI y (sF τ).sig ≠ 0 := by
      intro h0
      rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, h0, nval_zero] at hn
      exact EReal.top_ne_zero hn
    refine ⟨hev0, ?_⟩
    rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, nval_of_ne hev0] at hn
    have : ((vV T.V (evI y (sF τ).sig) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) = 0 := by exact_mod_cast hn
    show vV T.V (evI y (sF τ).sig) = 0
    simpa using this
  have hinv : ∀ τ, ev (sF τ).inv ∈ unitsV T := fun τ => by
    have e : ev (sF τ).sig * ev (sF τ).inv = 1 := by
      rw [← map_mul, (sF τ).mul_inv]; exact hid
    have h2 : ev (sF τ).inv ≠ 0 := right_ne_zero_of_mul_eq_one e
    refine ⟨h2, ?_⟩
    have h3 := vV_mul (V := T.V) (hsig τ).1 h2
    rw [e, (hsig τ).2, zero_add, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    exact h3.symm
  have hprod : ev s.sig ∈ unitsV T := by
    rw [(FlatSec.shift_spec hp sF w).1, map_mul, map_prod]
    refine (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).prod_mem fun τ _ => ?_)
    rw [(ConstSec.zpow_spec (sF τ) (-w τ)).1, map_mul, map_mul, map_pow, map_pow]
    exact (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).mul_mem ((unitsV T).pow_mem (hsig τ) _) ((unitsV T).pow_mem (hinv τ) _))
  exact hprod.2

end Gen

end GlobalTheory.FlatValZero

open GlobalTheory.FlatValZero

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.FlatValZero.flat_val_zero : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∀ w : AllWt.Psi p.T.Q.H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) w) 0), vV T.V (evI y' t.sig) = 0 := by
  intro hP hD _ hF
  have F := GlobalTheory.CovTop.FlatVal.flat_val hF
  unfold Covers Lifts at *
  refine (hD.and F).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY Z TF y T io y' g hg hpt hZ w => ?_⟩
  obtain ⟨-, hB⟩ := hx0 x hx hle ι p hp
  have hFE := (hB i hi Y hY).2.2.1
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  obtain ⟨t, ht⟩ := GlobalTheory.FlatValZero.twSec_flat_val hP hL hFE Z w
  refine ⟨t, ht T io y' (fun a ha => ?_) hZ⟩
  have ho : ∀ a, io a ∈ (algebraMap T.V T.Fr).range := fun a => by
    letI := io.toAlgebra
    have h1 := ptY_str TF.X y'.1
    rw [hpt, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc] at h1
    obtain ⟨b, hb⟩ := Spec.map_surjective
      (Spec.map (CommRingCat.ofHom g) ≫ ((Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ≫ flagStr TF.X)
    rw [← hb, ← Spec.map_comp] at h1
    exact ⟨b.hom a, congrArg (fun q => CommRingCat.Hom.hom q a) (Spec.map_injective h1)⟩
  have ha' : io a ≠ 0 := (map_ne_zero io).2 ha
  have h1 := (GlobalTheory.KeyValZero.mem_range_iff T _).1 (ho a)
  have h2 := (GlobalTheory.KeyValZero.mem_range_iff T _).1 (ho a⁻¹)
  have h3 := vV_mul (V := T.V) ha' ((map_ne_zero io).2 (inv_ne_zero ha))
  rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
  omega

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLaw
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem Chart.zero_app_eq {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k] (G : PDivGroup p k)
    (n : ℕ) (a : G.A n) :
    (0 : G ⟶ G).app n a = algebraMap k _ (Coalgebra.counit (R := k) a) := by
  have h := congrArg (fun u : WithConv (G.A n →ₐ[k] G.A n) => u.ofConv a)
    (map_one (toPts (R := k) (A := G.A n) (C := G.A n)))
  simp only [toPts_ofConv] at h
  exact h.trans (AlgHom.convOne_apply _)

theorem Chart.isMapOf_nmul : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ)
    (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ j : ℕ, c.IsMapOf c ((j : ℤ_[p]) • 𝟙 G) (nmul μ j) := by
  intro p _ k _ d G c μ hμ j
  induction j with
  | zero =>
    intro n i
    rw [Nat.cast_zero, zero_smul, Chart.zero_app_eq, c.aug, map_zero]
    show c.ev n ((fun _ => (0 : MvPowerSeries (Fin d) k)) i) = 0
    exact map_zero _
  | succ j ih =>
    have hX : c.IsMapOf c (𝟙 G) (fun i => (X i : MvPowerSeries (Fin d) k)) := fun n i => by
      rw [Chart.ev_X, id_app]; rfl
    have e1 : ((j + 1 : ℕ) : ℤ_[p]) • 𝟙 G = (j : ℤ_[p]) • 𝟙 G + 𝟙 G := by
      rw [Nat.cast_succ, add_smul, one_smul]
    have e2 : nmul μ (j + 1) = op μ (nmul μ j) (fun i => X i) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2]
    exact Chart.isMapOf_add p k d d G G c c μ _ _ _ _ hμ ih hX

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianRingStalk
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TraitCen

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω]

theorem isNoetherianRing_stalk (M : RatModel o' Ω) (x : M.Z) : IsNoetherianRing (M.Z.presheaf.stalk x) := by
  have : IsDedekindDomain o' := ArithBase.ded (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  infer_instance

theorem isDomain_stalk (M : RatModel o' Ω) (x : M.Z) : IsDomain (M.Z.presheaf.stalk x) :=
  (M.stalkHom_injective x).isDomain _

theorem charZero_stalk (M : RatModel o' Ω) (x : M.Z) : CharZero (M.Z.presheaf.stalk x) := by
  have : CharZero Ω := ArithBase.char (o := o')
  exact ⟨fun a b e => Nat.cast_injective (R := Ω) (by simpa using congrArg (M.stalkHom x) e)⟩

theorem exists_cdvr (M : RatModel o' Ω) (U₀ : M.Z.Opens) (hU : (U₀ : Set M.Z).Nonempty) (x : M.Z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W)
      (_ : IsAdicComplete (maximalIdeal W) W) (a : Sp W ⟶ M.Z),
      a (closedPoint W) = x ∧ ∀ t, (jK W ≫ a) t ∈ U₀ := by
  let O := M.Z.presheaf.stalk x
  have : IsNoetherianRing O := isNoetherianRing_stalk M x
  have : IsDomain O := isDomain_stalk M x
  have : CharZero O := charZero_stalk M x

  have hη : genericPoint M.Z ∈ U₀ := by
    obtain ⟨z, hz⟩ := hU
    exact (genericPoint_specializes z).mem_open U₀.isOpen hz
  have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes x
  obtain ⟨q, hq⟩ := h1
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := q) (show q ∈ (M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z) from by simpa [hq] using hη)
    (U₀.isOpen.preimage (M.Z.fromSpecStalk x).continuous)
  have hf₀ : f₀ ≠ 0 := fun h => hqf (by simp [h])

  let κ := ResidueField (PowerSeries O)
  let p := ringChar κ
  let c : PowerSeries O := if p = 0 then 1 else (p : PowerSeries O)
  have hc0 : c ≠ 0 := by
    by_cases hp : p = 0
    · simp [c, hp]
    · simp only [c, hp, if_false]
      rw [← map_natCast (PowerSeries.C (R := O))]
      exact (map_ne_zero_iff _ (PowerSeries.C_injective)).2 (Nat.cast_ne_zero.2 hp)
  let f : PowerSeries O := PowerSeries.X * PowerSeries.C f₀ * c
  have hfm : f ∈ maximalIdeal (PowerSeries O) := by
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hf0 : f ∉ (⊥ : Ideal (PowerSeries O)) := by
    rw [Ideal.mem_bot]
    exact mul_ne_zero (mul_ne_zero PowerSeries.X_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hf₀)) hc0
  let φ : PowerSeries O →+* AlgebraicClosure κ := (algebraMap κ (AlgebraicClosure κ)).comp (residue (PowerSeries O))
  obtain ⟨W, _, _, _, hW, ψ, ιk, hψf, hψ⟩ :=
    GlobalTheory.GeomTrait.exists_dvr hfm ⊥ Ideal.isPrime_bot hf0 φ
  let ψ' : O →+* W := ψ.comp PowerSeries.C
  have hψloc : IsLocalHom ψ := ⟨fun a ha => isUnit_of_map_unit φ a (by
    have h := (ha.map (residue W)).map ιk
    rw [← hψ]
    exact h)⟩
  have hCloc : IsLocalHom (PowerSeries.C (R := O)) := ⟨fun a ha => by
    simpa using ha.map (PowerSeries.constantCoeff (R := O))⟩
  have hψ'loc : IsLocalHom ψ' := RingHom.isLocalHom_comp ψ _
  have hψ'f₀ : ψ' f₀ ≠ 0 := fun h => hψf (by
    simp only [f, map_mul]
    rw [show ψ (PowerSeries.C f₀) = ψ' f₀ from rfl, h, mul_zero, zero_mul])
  have hcz : CharZero W := by
    obtain ⟨q, hq⟩ := CharP.exists W
    rcases CharP.char_is_prime_or_zero W q with hqp | hq0
    · exfalso
      have hqW : (q : W) = 0 := CharP.cast_eq_zero W q
      have hqκ : (q : κ) = 0 := by
        have h := congrArg (ιk.comp (residue W)) hqW
        rw [map_natCast, map_zero] at h
        refine (map_eq_zero_iff (algebraMap κ (AlgebraicClosure κ)) (algebraMap κ _).injective).1 ?_
        rw [map_natCast]
        exact h
      have : CharP κ q := (CharP.charP_iff_prime_eq_zero hqp).2 hqκ
      have hpq : p = q := ringChar.eq κ q
      have hp : p ≠ 0 := hpq ▸ hqp.ne_zero
      apply hψf
      have hc : c = (q : PowerSeries O) := by simp only [c, if_neg hp, hpq]
      show ψ (PowerSeries.X * PowerSeries.C f₀ * c) = 0
      rw [hc, map_mul, map_natCast, hqW, mul_zero]
    · subst hq0
      exact CharP.charP_to_charZero W
  let a : Sp W ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ') ≫ M.Z.fromSpecStalk x
  refine ⟨W, inferInstance, inferInstance, inferInstance, hcz, hW, a, ?_, fun t => ?_⟩
  · have h : (Spec.map (CommRingCat.ofHom ψ')) (closedPoint W) = closedPoint O := IsLocalRing.comap_closedPoint ψ'
    show M.Z.fromSpecStalk x ((Spec.map (CommRingCat.ofHom ψ')) (closedPoint W)) = x
    rw [h, Scheme.fromSpecStalk_closedPoint]
  · have ht : (jK W) t = (⊥ : PrimeSpectrum W) := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
    have hm : (PrimeSpectrum.comap ψ' ⊥ : PrimeSpectrum O) ∈ (PrimeSpectrum.basicOpen f₀ : Set (PrimeSpectrum O)) := by
      show f₀ ∉ Ideal.comap ψ' ⊥
      rw [Ideal.mem_comap, Ideal.mem_bot]
      exact hψ'f₀
    have := hf hm
    simp only [a, Scheme.Hom.comp_apply, ht]
    exact this

theorem exists_trait_cen : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o']
    [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty →
    ∀ (X : Scheme.{0}) (u₀ : U₀.toScheme ⟶ X) (u : X ⟶ F.X) (x : M.Z), IsClosed ({x} : Set M.Z) →
      ∃ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ u₀ u T ξ ∧ ξ (IsLocalRing.closedPoint T.V) = x := by
  intro g n o _ ζ F o' Ω _ _ _ _ M U₀ hU X u₀ u x _
  obtain ⟨W, _, _, _, _, hc, a, ha, hg⟩ := exists_cdvr M U₀ hU x
  have hr : Set.range (jK W ≫ a) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg t
  let ξ₀' : Sp (FractionRing W) ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (jK W ≫ a) hr
  have hξ₀' : ξ₀' ≫ U₀.ι = jK W ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hB : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hloc, -, hcomp, hy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n o ζ F W hB inferInstance (ξ₀' ≫ u₀ ≫ u)
  refine ⟨T, spMap f ≫ a, ⟨spMap fK ≫ ξ₀', ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hξ₀', ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hcomp r
  · rw [hy, Category.assoc]
  · have h : (spMap f) (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    show a ((spMap f) (closedPoint T.V)) = x
    rw [h, ha]

end GlobalTheory.Poinc.TraitCen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedClosedFibreProperCompleteLocalNoetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreconnected_closedFibre_proper_completeLocalNoetherian : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A], IsAdicComplete (maximalIdeal A) A → ∀ (X : Scheme.{0}) (f : X ⟶ Sp A), IsProper f → PreconnectedSpace X → _root_.IsPreconnected {x : X | f x = closedPoint A} := by
  first | exact @GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre | exact GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre | (intros; apply GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIrreducibleProperSpecialFibreCompleteD
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibreProper

theorem isProper_of_irreducible_of_isProper_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of O)), IrreducibleSpace X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → (∃ x : X, f x = IsLocalRing.closedPoint O) → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsProper f := by
  intro O _ _ _ _ X f hirr hsep hlft hqc hx hfib
  obtain ⟨x₀, hx₀⟩ := hx
  have hne : Nonempty X := ⟨x₀⟩
  obtain ⟨Y, P, π, q, s, U, hπ, hUne, hiso, hproj, hq, hcomm⟩ :=
    GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver O X f hsep hlft hqc hne
  have hs : IsProper s := by
    obtain ⟨N, i, hi, rfl⟩ := hproj
    have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
    infer_instance
  set C : Set Y := π ⁻¹' (U : Set X) with hC
  have hsurj : Function.Surjective (π ∣_ U) := fun y =>
    ⟨(inv (π ∣_ U)) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩

  have hUsub : (U : Set X) ⊆ π '' C := by
    intro u hu
    obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
    refine ⟨v.1, v.2, ?_⟩
    have := congrArg Subtype.val hv
    rwa [morphismRestrict_base_coe] at this

  have hUirr : IsIrreducible (U : Set X) :=
    ⟨hUne, (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩
  have hCirr : IsIrreducible C := by
    haveI : IrreducibleSpace (U : Set X) := Subtype.irreducibleSpace hUirr
    haveI : IrreducibleSpace (π ⁻¹ᵁ U).toScheme :=
      (Scheme.homeoOfIso (asIso (π ∣_ U))).irreducibleSpace_iff.2 (inferInstanceAs (IrreducibleSpace (U : Set X)))
    have h := (IrreducibleSpace.isIrreducible_univ (π ⁻¹ᵁ U).toScheme).image (fun y => (π ⁻¹ᵁ U).ι y)
      ((π ⁻¹ᵁ U).ι.continuous.continuousOn)
    convert h using 1
    ext y
    constructor
    · intro hy; exact ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨v, -, rfl⟩; exact v.2

  have hπT : π '' closure C = Set.univ := by
    have hcl : IsClosed (π '' closure C) := π.isClosedMap _ isClosed_closure
    have hd : Dense (U : Set X) := U.isOpen.dense hUne
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hd.closure_eq]
    exact closure_minimal (hUsub.trans (Set.image_mono subset_closure)) hcl
  have hmeet : ∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O := by
    obtain ⟨y, hy, hyx⟩ : x₀ ∈ π '' closure C := hπT ▸ Set.mem_univ x₀
    refine ⟨y, hy, ?_⟩
    rw [hcomm, Scheme.Hom.comp_apply, hyx, hx₀]
  have hfib' : IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) := by
    rw [hcomm, (Iso.eq_inv_comp (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) π)).2
      (pullbackRightPullbackFstIso_hom_snd (f := f) (g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) (f' := π))]
    infer_instance
  have hclosed := GlobalTheory.T.isClosed_image_closure_completeDVR_specialFibre O Y P q s C hs hq hfib' hCirr hmeet
  have huc : UniversallyClosed f :=
    GlobalTheory.T.universallyClosed_of_closed_image_cover _ X Y P f π q s (closure C) inferInstance hq hcomm isClosed_closure hclosed hπT
  exact ⟨⟩

end GlobalTheory.FibreProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelBaseChangeMap
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem trace_definite_forms_identity : TraceDefinitePairsEqAutomorphicTrace := by
  intro p _ G ha V _ _ _ ξ wt hξ L f hf hfb K' f' hf' hf'b hvan
  rw [GlobalTheory.T.bi_invariant_test_function_sum p G ha wt L f hf hfb K' f' hf' hf'b]
  unfold dTrace
  refine finsum_congr (fun q => ?_)
  rw [GlobalTheory.T.heckeTrace_definiteForm_eq_sum_conjClasses p G ha V ξ L f hf hfb K' f' hf' hf'b (Quot.out q)]
  refine finsum_congr (fun c => ?_)
  split_ifs with h
  · rw [hξ (Quot.out q) (Quotient.out c) h.1 h.2.1]
  · rw [GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero p G ha L f hf hfb K' f' hf' hf'b (Quot.out q) (Quotient.out c)
      (hvan (Quot.out q) _ _ _ (Quotient.out c) h), mul_zero]

end GlobalTheory.LKDef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRestrictionBijectiveLowDegreesStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_restriction_bijective_low_degrees : ∀ (D : Data) (Λ : Lift D), ((KK D.κ D.t).resMap Λ.L).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.Lift.resMap_lift_pullbackBijectiveDegreesOneTwo | exact GlobalTheory.PDForm.Lift.resMap_lift_pullbackBijectiveDegreesOneTwo | (intros; apply GlobalTheory.PDForm.Lift.resMap_lift_pullbackBijectiveDegreesOneTwo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleAdicReductions
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem lbIso_of_compatible_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ c : ∀ e, LB.Iso (A.pull (b e)) (A'.pull (b e)), (∀ e, (c e).IsGen) → (∀ e z k k', b e z ∈ A.U k → b e z ∈ A'.U k' → Geo.Tor.gw (c (e + 1)) (β e) z k' (fun _ => k) = Geo.Tor.gw (c e) (𝟙 _) z k' (fun _ => k)) → LBIso A A' := by
  intro R _ _ I hI X hX Y β b hpb hβ A A' hA hA' c hc hcomp
  have hle : ∀ e (p : (LB.div A' A).ι), b e ⁻¹ᵁ (LB.div A' A).U p ≤
      (LB.div (A'.pull (b e)) (A.pull (b e))).U (fun _ => p.1, fun _ => p.2) :=
    fun e p x hx => ⟨Set.mem_iInter.2 fun _ => hx.1, Set.mem_iInter.2 fun _ => hx.2⟩
  let s : ∀ e (i : (LB.div A' A).ι), Γ((Y e).left, b e ⁻¹ᵁ (LB.div A' A).U i)ˣ :=
    fun e p => res (hle e p) ((c e).s (fun _ => p.1, fun _ => p.2))
  have hs : ∀ e (z : (Y e).left) (p : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      gm (𝟙 _) z _ (s e p) = gw (c e) (𝟙 _) z p.1 (fun _ => p.2) :=
    fun e z p h => gm_res (𝟙 (Y e).left) z (hle e p) (by simpa using h) _
  have hg : ∀ e (z : (Y e).left) (p p' : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      b e z ∈ (LB.div A' A).U p' →
      gm (b e) z _ ((LB.div A' A).g p p') =
        gm (b e) z _ (A'.g p.1 p'.1) * (gm (b e) z _ (A.g p.2 p'.2))⁻¹ := by
    intro e z p p' h h'
    have hm : b e z ∈ (LB.div A' A).U p ⊓ (LB.div A' A).U p' := ⟨h, h'⟩
    show gm (b e) z _ (res _ (A'.g p.1 p'.1) * (res _ (A.g p.2 p'.2))⁻¹) = _
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ _ _ hm _)
      ((map_inv _ _).trans (congrArg _ (gm_res _ _ _ hm _))))
  have hpg : ∀ e (z : (Y e).left) (k k' : A.ι), b e z ∈ A.U k → b e z ∈ A.U k' →
      gm (𝟙 (Y e).left) z _ ((A.pull (b e)).g (fun _ => k) (fun _ => k')) =
        gm (b e) z _ (A.g k k') := by
    intro e z k k' hk hk'
    have hp : (𝟙 (Y e).left) z ∈ (A.pull (b e)).U (fun _ => k) ⊓ (A.pull (b e)).U (fun _ => k') :=
      ⟨mem_pull.2 hk, mem_pull.2 hk'⟩
    show gm _ z _ (∏ _k : PUnit, (res _ (pullU (b e) _ (A.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z _ hp _).trans ((gm_pull (𝟙 _) (b e) z (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans
      (by rw [Category.id_comp]))
  refine (GlobalTheory.T.exists_generator_algebraisation_reductions R I hI X hX Y β b hpb hβ (LB.div A' A) (LB.isLB_div hA' hA) s ?_ ?_ :
    ∃ t : LB.Gen (LB.div A' A), t.IsGen)
  · intro e z p p' h h'
    rw [hs e z p h, hs e z p' h', hg e z p p' h h']
    have := (isGen_iff (c e)).1 (hc e) _ (𝟙 _) z p.1 p'.1 (fun _ => p.2) (fun _ => p'.2) h.1 h'.1
      (mem_pull.2 h.2) (mem_pull.2 h'.2)
    rw [this, hpg e z p.2 p'.2 h.2 h'.2, Category.id_comp]
  · intro e z p h
    have h1 : b (e + 1) (β e z) = b e z := by rw [← hβ e]; rfl
    have hz : β e z ∈ b (e + 1) ⁻¹ᵁ (LB.div A' A).U p := show b (e + 1) (β e z) ∈ _ from h1 ▸ h
    rw [show gm (β e) z _ (s (e + 1) p) = gw (c (e + 1)) (β e) z p.1 (fun _ => p.2) from
      gm_res _ z (hle (e + 1) p) hz _, hcomp e z p.2 p.1 h.2 h.1, hs e z p h]

end GlobalTheory.FormalAlg
end

