import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomShInvOfGIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O

namespace Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem regAt_φ {x : V.G} {f : Y.Fn} (h : RegAt (V.π x) f) : RegAt x (V.φ f) := by
  obtain ⟨hη, e⟩ := GlobalTheory.T.cover_function_field_map_eq V
  rw [e]
  obtain ⟨U, hx, s, rfl⟩ := h.exists_fnOf
  have hy : x ∈ V.π ⁻¹ᵁ U := hx
  rw [SmallSec.fnMap_fnOf V.π hη _ (gen_mem hy)]
  exact regAt_fnOf hy _ _

theorem unitAt_φ {x : V.G} {f : Y.Fn} (h : UnitAt (V.π x) f) : UnitAt x (V.φ f) := by
  have h0 : f ≠ 0 := h.ne_zero
  rw [unitAt_iff ((map_ne_zero V.φ).2 h0), ← map_inv₀]
  exact ⟨V.regAt_φ h.regAt, V.regAt_φ h.inv.regAt⟩

theorem valAt_φ {K : Type} [Field K] (z : Sp K ⟶ V.G) {f : Y.Fn} (h : RegAt (V.π (below z)) f) :
    valAt z (V.φ f) = valAt (z ≫ V.π) f := by
  obtain ⟨hη, e⟩ := GlobalTheory.T.cover_function_field_map_eq V
  rw [e]
  exact SmallSec.valAt_fnMap V.π hη z h

theorem ratVal_φ {σ : F →+* ℂ} (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (e : y.1 = z.1 ≫ V.π) {f : Y.Fn}
    (h : RegAt (under y) f) : ratVal (V.φ f) z = ratVal f y := by
  have hu : V.π (below z.1) = under y := by
    show _ = y.1 _
    rw [e]
    rfl
  rw [← hu] at h
  rw [SmallSec.ratVal_eq_valAt z (V.regAt_φ h), V.valAt_φ z.1 h, ← e, SmallSec.ratVal_eq_valAt y (hu ▸ h)]

theorem unitAt_genAt_mul_genAt {D D' : Y.Dv} (hD : D' = -D) (x : Y.X) : UnitAt x (genAt D' x * genAt D x) := by
  have h1 : D'.IsEqn x (eqn D x)⁻¹ := hD ▸ (Base.isEqn_eqn D x).neg
  have h2 := (Base.isEqn_eqn D' x).iff_unitAt.1 h1
  convert h2 using 1
  simp only [genAt, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  ring

theorem induces_dual {C : CxSt F} (A A' : Adl C Y) (L : HermLB V.p)
    (hD : A'.D = -A.D) (hc : A.ci = 0) (hc' : A'.ci = 0)
    (hm : ∀ σ (y : Pts Y σ) (f : Y.Fn), A.D.GeneratesAt (under y) f →
      C.pn Y σ A.D (A.m σ) (C.cx Y σ f) y * C.pn Y σ A'.D (A'.m σ) (C.cx Y σ f⁻¹) y = 1)
    (hlg : ∀ v e (y : AlgPt Y), A'.lg v e y = -A.lg v e y +
      Real.log (e.w (valAt y.1 (genAt A'.D (below y.1) * genAt A.D (below y.1)))))
    (h : V.Induces A L 1) : V.Induces A' L.dual 1 := by
  obtain ⟨r, hr, hun, hcx, hfin⟩ := h
  have hu := unitAt_genAt_mul_genAt hD

  have key : ∀ (i : (L.B.pull V.j).ι) (x : V.G), x ∈ (L.B.pull V.j).U i →
      V.φ (genAt A'.D (V.π x)) ^ 1 * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField) =
        V.φ (genAt A'.D (V.π x) * genAt A.D (V.π x)) * (V.φ (genAt A.D (V.π x)) ^ 1 * r i)⁻¹ := by
    intro i x _
    have h0 : V.φ (genAt A.D (V.π x)) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
    have h0' : ((r i : V.G.functionFieldˣ) : V.G.functionField) ≠ 0 := Units.ne_zero _
    rw [map_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hunit : ∀ (i : (L.B.pull V.j).ι) (x : V.G), x ∈ (L.B.pull V.j).U i →
      UnitAt x (V.φ (genAt A'.D (V.π x)) ^ 1 * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) := by
    intro i x hx
    rw [key i x hx]
    exact (V.unitAt_φ (hu (V.π x))).mul (hun i x hx).inv
  refine ⟨fun i => (r i)⁻¹, ?_, hunit, ?_, ?_⟩
  · intro i j hij
    have e := hr i j hij
    have e' : fnOf _ hij (((CechPic.dual L.B).pull V.j).g i j).val = (fnOf _ hij ((L.B.pull V.j).g i j).val)⁻¹ :=
      (congrArg (fun u : Γ(V.G, (L.B.pull V.j).U i ⊓ (L.B.pull V.j).U j)ˣ => fnOf _ hij u.val)
        (GlobalTheory.LineNorm.Neg.pull_dual_g L.B V.j i j)).trans (map_units_inv _ _)
    refine Eq.trans ?_ (congrArg (· * _) e').symm
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, e, mul_inv]
    rfl
  · intro σ z y y' i e1 e2 hi
    have H := hcx σ z y y' i e1 e2 hi
    simp only [hc, hc', Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul, pow_one] at H ⊢
    rw [show (L.dual.φ _).φ (i PUnit.unit) y' = -((L.φ _).φ (i PUnit.unit) y') from rfl]
    have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e1]
      rfl
    have hx : under z ∈ (L.B.pull V.j).U i := hi
    have hU1 := hunit i _ hx
    have hU2 := hun i _ hx
    rw [hπ] at hU1 hU2
    simp only [pow_one] at hU1 hU2
    set g := genAt A.D (under y) with hg
    set g' := genAt A'.D (under y) with hg'
    have hg0 : g ≠ 0 := Units.ne_zero _
    have hg0' : g' ≠ 0 := Units.ne_zero _
    have k1 := hm σ y g (generatesAt_genAt A.D _)
    have hinv : g⁻¹ = (g' * g)⁻¹ * g' := by field_simp
    have k2 : C.pn Y σ A'.D (A'.m σ) (C.cx Y σ g⁻¹) y =
        ‖ratVal (g' * g)⁻¹ y‖ ^ 2 * C.pn Y σ A'.D (A'.m σ) (C.cx Y σ g') y := by
      rw [hinv]
      exact C.pn_mul Y σ A'.D (A'.m σ) _ _ y (hu _).inv.regAt (generatesAt_genAt A'.D _).regularAt
    have k3 : ratVal (g' * g)⁻¹ y * ratVal (g' * g) y = 1 := by
      rw [← ratVal_mul (hu _).inv.regAt (hu _).regAt, inv_mul_cancel₀ (hu _).ne_zero, Base.ratVal_one]
    have k4 : ratVal (V.φ g' * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) z *
        ratVal (V.φ g * (r i : V.G.functionField)) z = ratVal (g' * g) y := by
      rw [← ratVal_mul hU1.regAt hU2.regAt, ← V.ratVal_φ z y e1 (hu _).regAt]
      congr 1
      have h0 : V.φ g ≠ 0 := (map_ne_zero _).2 hg0
      have h0' : ((r i : V.G.functionFieldˣ) : V.G.functionField) ≠ 0 := Units.ne_zero _
      rw [map_mul, Units.val_inv_eq_inv_val, mul_mul_mul_comm, inv_mul_cancel₀ h0', mul_one]
    have k3' : ‖ratVal (g' * g)⁻¹ y‖ ^ 2 * ‖ratVal (g' * g) y‖ ^ 2 = 1 := by
      rw [← mul_pow, ← norm_mul, k3, norm_one, one_pow]
    have k4' : ‖ratVal (V.φ g' * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) z‖ ^ 2 *
        ‖ratVal (V.φ g * (r i : V.G.functionField)) z‖ ^ 2 = ‖ratVal (g' * g) y‖ ^ 2 := by
      rw [← mul_pow, ← norm_mul, k4]
    rw [k2] at k1
    have hE : Real.exp (-(L.φ _).φ (i PUnit.unit) y') * Real.exp (-(-(L.φ _).φ (i PUnit.unit) y')) = 1 := by
      rw [← Real.exp_add]; simp
    set P := C.pn Y σ A.D (A.m σ) (C.cx Y σ g) y
    set Q := C.pn Y σ A'.D (A'.m σ) (C.cx Y σ g') y
    set c2 := ‖ratVal (g' * g) y‖ ^ 2
    set a2 := ‖ratVal (V.φ g' * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) z‖ ^ 2
    set b2 := ‖ratVal (V.φ g * (r i : V.G.functionField)) z‖ ^ 2
    set ep := Real.exp (-(-(L.φ _).φ (i PUnit.unit) y'))
    have hP : P ≠ 0 := left_ne_zero_of_mul_eq_one k1
    refine mul_left_cancel₀ hP ?_
    linear_combination c2 * k1 - (P * Q) * k3' - (a2 * ep) * H - (a2 * b2) * hE - k4'
  · intro v e y z yt i e1 e2 hi
    have H := hfin v e y z yt i e1 e2 hi
    have hmem : below z ∈ (L.B.pull V.j).U i := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit) := by
        rw [← e2]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e1]
      rfl
    have hU1 := hunit i _ hmem
    have hU2 := hun i _ hmem
    rw [hπ] at hU1 hU2
    simp only [pow_one, Nat.cast_one, one_mul] at hU1 hU2 H ⊢
    have h0 : V.φ (genAt A.D (below y.1)) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
    have e3 : V.φ (genAt A'.D (below y.1)) * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField) =
        V.φ (genAt A'.D (below y.1) * genAt A.D (below y.1)) *
          (V.φ (genAt A.D (below y.1)) * (r i : V.G.functionField))⁻¹ := by
      rw [map_mul, Units.val_inv_eq_inv_val, mul_inv, ← mul_assoc, mul_assoc (V.φ (genAt A'.D (below y.1))),
        mul_inv_cancel₀ h0, mul_one]
    have hu' : UnitAt (V.π (below z)) (genAt A'.D (below y.1) * genAt A.D (below y.1)) := by
      rw [hπ]; exact hu _
    have hφu : UnitAt (below z) (V.φ (genAt A'.D (below y.1) * genAt A.D (below y.1))) := V.unitAt_φ hu'
    have n1 : e.w (valAt y.1 (genAt A'.D (below y.1) * genAt A.D (below y.1))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero (hu _))
    have n2 : e.w (valAt z (V.φ (genAt A.D (below y.1)) * (r i : V.G.functionField))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero hU2)
    rw [e3, SmallSec.valAt_mul hφu.regAt hU2.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv hU2, V.valAt_φ z hu'.regAt, e1,
      map_mul, map_inv₀, Real.log_mul n1 (inv_ne_zero n2), Real.log_inv, ← H, hlg]
    ring

end Cover

theorem Setup.induces_root0 : ∀ (D : D7) (O : Setup D), O.DualRef → ∀ (P : Finset ℕ) (c : O.s.Comp) (W : O.LatModel P c)
    (Q : Finset ℕ), Q ⊆ P → ∀ x : DV.Rt D.what₂.Tau O.N, W.V.Induces (O.root0 c Q x) (W.root Q x) 1 := by
  intro D O hdr P c W Q hQ x
  have hp : O.S.Dw.p = O.j := O.S.p_eq
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hτ : O.S.Dw.mult (DV.tauEmb D x.1) = O.j := GlobalTheory.LocM.Check.mult_tau (S := O.S) x.1
  have hcj : O.S.Dw.mult (conjEmb (DV.tauEmb D x.1)) + O.j = O.N := GlobalTheory.LocM.Check.mult_conj (S := O.S) x.1
  have hx2 : (x.2 : ℕ) < O.N := x.2.2
  unfold LatModel.root Setup.root0 rootSym
  by_cases h : (x.2 : ℕ) < O.j
  · rw [if_pos h, if_pos (show (x.2 : ℕ) < O.S.Dw.p by omega)]
    refine W.line_spec Q hQ _ ?_
    simp [letterOf, hτ, h]
  · rw [if_neg h, if_neg (by omega), show O.S.Dw.p + O.S.Dw.q - 1 - (x.2 : ℕ) = O.N - 1 - x.2 by omega]
    set st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ := .inl (conjEmb (DV.tauEmb D x.1), O.N - 1 - (x.2 : ℕ)) with hst
    have hs : (letterOf O.S.Dw st).isSome := by
      have : O.N - 1 - (x.2 : ℕ) < O.S.Dw.mult (conjEmb (DV.tauEmb D x.1)) := by omega
      simp [hst, letterOf, this]
    have hL := W.line_spec Q hQ st hs
    have hex : ∀ m : ℤ, expo O.S.Dw (Finsupp.single (ArIn.ind Q, none, st) m) = m • expo O.S.Dw (Finsupp.single (ArIn.ind Q, none, st) 1) := by
      intro m
      funext y
      simp only [expo_single, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    have hex0 : O.ex x = expo O.S.Dw (Finsupp.single (ArIn.ind Q, none, st) (-1)) := by
      unfold Setup.ex rootEx rootSym
      rw [if_neg (show ¬ ((x.2 : ℕ) < O.S.Dw.p) by omega),
        show O.S.Dw.p + O.S.Dw.q - 1 - (x.2 : ℕ) = O.N - 1 - x.2 by omega]
      funext y
      simp only [expo_single, hst]
    have hD : ∀ n : Letter O.S.Dw → ℤ, divOf (O.Φ.C c) (-n) = -divOf (O.Φ.C c) n := by
      intro n
      simp [divOf, neg_smul, Finset.sum_neg_distrib]
    have gen : ∀ n₁ n₂ : Letter O.S.Dw → ℤ, n₁ = -O.ex x → n₂ = O.ex x → ∀ σ (y : Pts (O.var c) σ) (f : (O.var c).Fn),
        (divOf (O.Φ.C c) n₁).GeneratesAt (under y) f →
        (cxSt _).pn _ σ _ (O.met.h0 c σ n₁) ((cxSt _).cx _ σ f) y *
          (cxSt _).pn _ σ _ (O.met.h0 c σ n₂) ((cxSt _).cx _ σ f⁻¹) y = 1 := by
      rintro n₁ n₂ rfl rfl σ y f hf
      have hf0 : f ≠ 0 := hf.ne_zero
      have h1 : (divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under y) f⁻¹ := by
        have h2 : (-divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under y) ((((Units.mk0 f hf0)⁻¹ : (O.var c).Fnˣ)) : (O.var c).Fn)⁻¹ := by
          rw [← hD]; simpa using hf
        have h3 := (CartierDiv.isEqn_iff_generatesAt_inv.2 h2).neg
        rw [neg_neg, inv_inv] at h3
        simpa using CartierDiv.isEqn_iff_generatesAt_inv.1 h3
      have := hdr c σ x y f⁻¹ h1
      rw [inv_inv, mul_comm] at this
      exact this
    refine W.V.induces_dual _ _ _ ?_ rfl rfl ?_ ?_ hL
    · show divOf _ _ = -divOf _ _
      rw [hex (-1), neg_one_smul, hD]
    · intro σ y f hf
      exact gen _ _ (by rw [hex0, hex (-1), neg_one_smul, neg_neg]) hex0.symm σ y f hf
    · intro v e y
      exact GlobalTheory.T.lgOf_single_neg_one_eq_neg (O.Φ.C c) (ArIn.ind Q, none, st) v e y

end GlobalTheory.Mean4O
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CompHS GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.FlagHodge

attribute [local instance] Over.cartesianMonoidalCategory

theorem ev_cocycle {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) {S : Type} [CommRing S] (z : Sp S ⟶ Z) (i j k : L.ι)
    (hij : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j)) (hjk : ⊤ ≤ z ⁻¹ᵁ (L.U j ⊓ L.U k)) (hik : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    ev z _ hij (L.g i j).val * ev z _ hjk (L.g j k).val = ev z _ hik (L.g i k).val := by
  have h3 : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_preimage_inf hij (le_preimage_mono inf_le_right hjk)
  have e := congrArg (fun u => ev z _ h3 u.val) (hL.cocycle i j k)
  exact (congrArg₂ (· * ·) (ev_res z _ h3 hij _).symm (ev_res z _ h3 hjk _).symm).trans
    ((map_mul (ev z _ h3) _ _).symm.trans (e.trans (ev_res z _ h3 hik _)))

theorem lbIso_of_coboundary {Z : Scheme.{0}} {J : Type} {U : J → Z.Opens} {g g' : ∀ i j, Γ(Z, U i ⊓ U j)ˣ}
    (hA : (⟨J, U, g⟩ : LB Z).IsLB) (d : ∀ k, Γ(Z, U k)ˣ)
    (h : ∀ k k', (g' k k').val * resG Z inf_le_right (d k').val = (g k k').val * resG Z inf_le_left (d k).val) :
    LBIso (⟨J, U, g⟩ : LB Z) ⟨J, U, g'⟩ := by
  refine ⟨⟨fun p => g p.1 p.2 * res inf_le_left (d p.1)⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ U p.1 := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ U q.1 := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ U p.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ U q.2 := le_preimage_mono inf_le_right hq
  have c₁ := ev_cocycle hA z p.1 p.2 q.2 hp (le_preimage_inf hp2 hq2) (le_preimage_inf hp1 hq2)
  have c₂ := ev_cocycle hA z p.1 q.1 q.2 (le_preimage_inf hp1 hq1) hq (le_preimage_inf hp1 hq2)
  have c₃ := congrArg (ev z _ (le_preimage_inf hp1 hq1)) (h p.1 q.1)
  rw [map_mul, map_mul, ev_res z _ _ hq1, ev_res z _ _ hp1] at c₃
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((map_mul (ev z _ hp) _ _).trans
    (congrArg (_ * ·) (ev_res z _ hp hp1 _)))) (ev_res z _ hz (le_preimage_inf hp2 hq2) _)).trans (Eq.trans ?_
    (congrArg₂ (· * ·) (ev_res z _ hz (le_preimage_inf hp1 hq1) _) ((ev_res z _ hz hq _).trans
      ((map_mul (ev z _ hq) _ _).trans (congrArg (_ * ·) (ev_res z _ hq hq1 _))))).symm)
  have alg : ∀ a b e m n u v w : S, a * b = e → m * n = e → w * v = m * u → a * u * b = w * (n * v) :=
    fun a b e m n u v w h₁ h₂ h₃ => by linear_combination u * (h₁ - h₂) - n * h₃
  exact alg _ _ _ _ _ _ _ _ c₁ c₂ c₃

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)

theorem exists_eigFrame {W : X.YY.Opens} (hW : IsAffineOpen W) {S : Type} [CommRing S] (z : Sp S ⟶ X.YY)
    (hzW : ⊤ ≤ z ⁻¹ᵁ W) : ∃ φ : c.F →+* S, ∀ (k : X.F.J) (_ : W ≤ X.F.U k) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k),
      ∃ f : EigFrame Y φ (z ≫ X.π), ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Γ(X.YY, W) →+* S, spMap ψ ≫ tau hW = z := ⟨_, spMap_ev z hW hzW⟩
  haveI := X.proper
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian X.YY := LocallyOfFiniteType.isLocallyNoetherian (X.π ≫ Y.s)
  obtain ⟨φ, hφ⟩ : ∃ φ : c.F →+* Γ(X.YY, W), spMap φ = tau hW ≫ X.π ≫ Y.s :=
    ⟨(Spec.preimage (tau hW ≫ X.π ≫ Y.s)).hom, Spec.map_preimage _⟩
  refine ⟨ψ.comp φ, fun k hk hz => ?_⟩
  obtain ⟨K, _, ρ, hρ, hK⟩ := affineOpen_injects_to_dense X.YY (flagOpen X) (dense_flagOpen X) W hW
  letI : Algebra c.F K := (ρ.comp φ).toAlgebra
  have h₀ : ⊤ ≤ tau hW ⁻¹ᵁ X.F.U k := tau_le hW hk
  have hz' : ⊤ ≤ (spMap ρ ≫ tau hW) ⁻¹ᵁ X.F.U k := le_preimage_comp _ h₀
  have hr : Set.range ((spMap ρ ≫ tau hW) ≫ X.π) ⊆ Set.range Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hK (Set.mem_univ s)
  let yK := IsOpenImmersion.lift Y.j ((spMap ρ ≫ tau hW) ≫ X.π) hr
  have hyK : yK ≫ Y.j = (spMap ρ ≫ tau hW) ≫ X.π := IsOpenImmersion.lift_fac _ _ _
  have hjs : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
      unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h1, Category.comp_id]
  have hy : yK ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← hjs, ← Category.assoc, hyK]
    have h2 : spMap ρ ≫ spMap φ = spMap (algebraMap c.F K) := by
      unfold spMap; rw [← Spec.map_comp]; rfl
    rw [← h2, hφ]
    simp only [Category.assoc]
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap ρ ≫ tau hW) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ tau hW) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.ChartEigFrame.exists_eigFrame_of_top ρ hρ φ rfl (tau hW) k h₀ hz'
    (key _ hyK.symm fun σ => X.top K yK hy _ hyK.symm k hz' σ)
  obtain ⟨f, hf⟩ := f₀.exists_isMap ψ rfl (Category.assoc _ _ _)
  refine ⟨f, fun τ => funext fun i => tan_ext_left ?_⟩
  rw [← X.F.tanPull_vecAt k ψ (tau hW) h₀ hz rfl rfl (Category.assoc _ _ _).symm τ i, tanPull_left, ← hf₀, ← hf]
  simp only [EigFrame.vec, GlobalTheory.LieMet.left_tanOf]

def allDet (k : X.F.J) : Γ(X.YY, X.F.U k) :=
  rdet (Matrix.of fun (j : Fin (X.F.M k).n) (a : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))) =>
    X.F.u k ((Fintype.equivFin _).symm a).1 j ((Fintype.equivFin _).symm a).2)

theorem ev_allDet (k : X.F.J) {S : Type} [CommRing S] {z : Sp S ⟶ X.YY} (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) {φ : c.F →+* S}
    {f : EigFrame Y φ (z ≫ X.π)} (hf : ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ) :
    ev z _ hz (allDet X k) = frameDet (X.F.M k).toMChart (X.F.inM hz rfl) f := by
  rw [allDet, map_rdet, frameDet]
  congr 1
  ext j a
  simp [Module.Basis.toMatrix_apply, eigBasisFin, eigBasis_apply, hf, Frames.vecAt, Frames.uAt, vec,
    Finsupp.single_apply]

theorem isUnit_allDet (k : X.F.J) : IsUnit (allDet X k) := by
  refine X.YY.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k) (x := x) hx
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW (tau hW) (tau_le hW le_rfl)
  obtain ⟨f, hf⟩ := hφ k hle (tau_le hW hle)
  have hu := isUnit_frameDet (X.F.M k).toMChart (X.F.inM (tau_le hW hle) rfl) f
  rw [← ev_allDet X k _ hf, ev_tau hW hle] at hu
  have := hu.map (X.YY.presheaf.germ W x hxW).hom
  rwa [show (X.YY.presheaf.germ W x hxW).hom (resG X.YY hle (allDet X k)) = _ from
    X.YY.presheaf.germ_res_apply (homOfLE hle) x hxW _] at this

theorem lbIso_detOm_Llam : LBIso X.detOm (X.Llam (mu0 Dw)) := by
  classical
  rw [FlagCover.Llam, unitaryWeightExponentVector_signatureWeightMuZero]
  refine lbIso_of_coboundary X.F.isLB_detOm (fun k => (isUnit_allDet X k).unit) fun k k' =>
    ext_ev_loc fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k ⊓ X.F.U k') (x := x) hx
  refine ⟨W, hxW, fun S _ z hh hzW => ?_⟩
  have hz := le_preimage_mono inf_le_left hh
  have hz' := le_preimage_mono inf_le_right hh
  have hM := le_preimage_inf (X.F.inM hz rfl) (X.F.inM hz' rfl)
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW z hzW
  obtain ⟨f, hf⟩ := hφ k (fun _ h => (hle h).1) hz
  obtain ⟨f', hf'⟩ := hφ k' (fun _ h => (hle h).2) hz'
  have hco : ∀ τ, f.co f' τ = (X.F.B k k' τ).map (ev z _ hh) := fun τ => by
    ext a i
    have e := f.vec_eq f' τ i
    rw [hf', X.F.vecAt_eq_sum k k' z hz hz' hh rfl τ i, ← hf] at e
    exact ((Fintype.linearIndependent_iffₛ.1 (f.linearIndependent_vec τ)) _ _ e a).symm
  have e₁ := (ev_detChg_mul_frameDet (X.F.M k).toMChart (X.F.M k').toMChart (X.F.inM hz rfl) (X.F.inM hz' rfl) hM
    f').trans (frameDet_change _ _ f f')
  have e₂ : ∏ τ, (f.co f' τ).det = (∏ p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), X.F.TAt k k' z hh (some p)).val := by
    rw [Units.coe_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hco, Matrix.det_of_upperTriangular (X.F.B_map_tri k k' τ _)]
    rfl
  have e₃ := X.F.ev_LL_g (fun ix => ix.elim 0 fun _ => 1) k k' z hh
  rw [Fintype.prod_option] at e₃
  simp only [Option.elim, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one, Finset.prod_inv_distrib] at e₃
  let a : Sˣ := Units.map (ev (z ≫ X.π) _ hM).toMonoidHom (detChg (X.F.M k).toMChart (X.F.M k').toMChart)
  have e₄ : ev z _ hh (X.F.detOm.g k k').val = (a⁻¹).val :=
    (ev_unit_inv z hh _).trans (congrArg (fun u : Sˣ => (u⁻¹).val) (Units.ext (ev_appLE z X.π _ hh hM _)))
  rw [← ev_allDet X k hz hf, ← ev_allDet X k' hz' hf', e₂] at e₁
  rw [map_mul, map_mul, ev_res z _ hh hz, ev_res z _ hh hz']
  refine (congrArg (· * _) e₃).trans (Eq.trans ?_ (congrArg (· * _) e₄).symm)
  rw [_root_.one_mul, Units.inv_mul_eq_iff_eq_mul, mul_left_comm, Units.eq_inv_mul_iff_mul_eq, _root_.mul_comm (Units.val _) (ev z _ hz _)]
  exact e₁

end GlobalTheory.FlagHodge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionAddAtGeometricPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem mul_comp_eq_of_isGrpPullback {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G]
    {G₁ : Over S₁} [GrpObj G₁] {G₂ : Over S₂} [GrpObj G₂] {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
    {ψ₁ : G₁.left ⟶ G.left} {ψ₂ : G₂.left ⟶ G.left}
    (h₁ : IsGrpPullback G₁ G f₁ ψ₁) (h₂ : IsGrpPullback G₂ G f₂ ψ₂) {T : Scheme.{0}}
    {t₁ : T ⟶ S₁} {t₂ : T ⟶ S₂} (ht : t₁ ≫ f₁ = t₂ ≫ f₂)
    (A₁ B₁ : Over.mk t₁ ⟶ G₁) (A₂ B₂ : Over.mk t₂ ⟶ G₂)
    (hA : A₁.left ≫ ψ₁ = A₂.left ≫ ψ₂) (hB : B₁.left ≫ ψ₁ = B₂.left ≫ ψ₂) :
    (A₁ * B₁).left ≫ ψ₁ = (A₂ * B₂).left ≫ ψ₂ := by
  have key : ∀ (u : T ⟶ S) (e₁ : t₁ ≫ f₁ = u) (e₂ : t₂ ≫ f₂ = u),
      (A₁ * B₁).left ≫ ψ₁ = (A₂ * B₂).left ≫ ψ₂ := by
    intro u e₁ e₂
    have wA : (A₁.left ≫ ψ₁) ≫ G.hom = u := by
      rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w A₁]; exact e₁
    have wB : (B₁.left ≫ ψ₁) ≫ G.hom = u := by
      rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w B₁]; exact e₁
    let a : Over.mk u ⟶ G := Over.homMk (A₁.left ≫ ψ₁) wA
    let b : Over.mk u ⟶ G := Over.homMk (B₁.left ≫ ψ₁) wB
    have p₁ : (a * b).left = (A₁ * B₁).left ≫ ψ₁ := by
      subst e₁
      exact h₁.2 (Over.mk t₁) A₁ B₁ a b rfl rfl
    have p₂ : (a * b).left = (A₂ * B₂).left ≫ ψ₂ := by
      subst e₂
      exact h₂.2 (Over.mk t₂) A₂ B₂ a b hA hB
    exact p₁.symm.trans p₂
  exact key _ ht rfl

theorem etaSecL_add_geom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (a b : LevelMod Dw l)
    (A B C : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ) (hA : A.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ a)
    (hB : B.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ b) (hC : C.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ (a + b)), C = A * B := by
  intro E _ _ _ H Dw l Xo c TF Z X' φ ℓ hℓ Ω _ _ x a b A B C hA hB hC
  obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [← Submodule.Quotient.mk_add] at hC
  let y : Sp Ω ⟶ Xo.XF c := x ≫ i₀ TF.Y Z
  let u : Over.mk y ⟶ 𝟙_ (Over (Xo.XF c)) := Over.homMk y (Category.comp_id y)
  have hψ : ∀ (d : Dw.La) (D : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ),
      D.left = x ≫ etaSecL TF Z φ ℓ hℓ (Submodule.Quotient.mk d) →
      D.left ≫ GlobalTheory.EqvAct.pullψ TF Z φ = (u ≫ TF.Y.oF.eta d).left ≫ TF.Y.m.φ := by
    intro d D hD
    rw [hD, Category.assoc, etaSecL_ψ]
    change _ = ((x ≫ i₀ TF.Y Z) ≫ (TF.Y.oF.eta d).left) ≫ TF.Y.m.φ
    simp only [Category.assoc]
  have ht : (x ≫ ℓ) ≫ φ ≫ (barComp TF.Y Z).ι = y ≫ TF.Y.j := by
    change _ = (x ≫ (TF.Y.j ⁻¹ᵁ barComp TF.Y Z).ι) ≫ TF.Y.j
    rw [Category.assoc, Category.assoc, ← Category.assoc ℓ, hℓ, morphismRestrict_ι]
  have hmul := mul_comp_eq_of_isGrpPullback (GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ) TF.Y.m.cart ht
    A B (u ≫ TF.Y.oF.eta a') (u ≫ TF.Y.oF.eta b') (hψ _ _ hA) (hψ _ _ hB)
  have hC' := hψ _ _ hC
  rw [TF.Y.oF.eta_add a' b', MonObj.comp_mul] at hC'
  ext1
  refine (GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ).1.hom_ext (hC'.trans hmul.symm) ?_
  rw [Over.w C, Over.w (A * B)]

end GlobalTheory.TorsSpec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisTorusExtensionOfLiftsAndDualsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.lieBasis_torusExtension_of_lifts_and_duals : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ D.X) (x : Fin D.P.g ⊕ Fin r → (epsR R ⟶ H)), IsLieBasis vB → (∀ j, GtTan (Φ _ (x j))) → (∀ i, (Φ _ (x (Sum.inl i))).b = vB i) → (∀ l, (Φ _ (x (Sum.inr l))).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x (Sum.inr l))).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : R)))) → ∀ (n : ℕ) (σ : Fin n ≃ Fin D.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := by
  first | exact @GlobalTheory.GtBasis.main | exact GlobalTheory.GtBasis.main | (intros; apply GlobalTheory.GtBasis.main <;> assumption) | exact @GlobalTheory.GtBasis.dn_inj | exact GlobalTheory.GtBasis.dn_inj | (intros; apply GlobalTheory.GtBasis.dn_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyTrivialUnitCocycleSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_trivial_unit_cocycle_scheme : ∀ (X Y Z W : Scheme.{0}) (p : X ⟶ Y) (a b : Z ⟶ X) (m₁₂ m₂₃ m₁₃ : W ⟶ Z) (χ : Γ(Z, ⊤)ˣ), IsAffineHom p → Flat p → Surjective p → IsPullback b a p p → IsPullback m₁₂ m₂₃ a b → m₁₃ ≫ b = m₁₂ ≫ b → m₁₃ ≫ a = m₂₃ ≫ a → pullTop m₁₃ χ = pullTop m₁₂ χ * pullTop m₂₃ χ → ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e : Γ(X, p ⁻¹ᵁ V)ˣ, ∀ (W' : Z.Opens) (h₁ : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V)) (h₂ : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V)), res h₁ (pullU a _ e) = res le_top χ * res h₂ (pullU b _ e) := by
  first | exact @GlobalTheory.CharKer.exists_local_charUnit | exact GlobalTheory.CharKer.exists_local_charUnit | (intros; apply GlobalTheory.CharKer.exists_local_charUnit <;> assumption)
end

