import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixDetNotMem
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RawSeriesMoveDatum
section
section Point

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.ChangePt

theorem move_at_point : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), IsSympl X bas → r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E), Λ.Unimod → IsUnitaryM h → Λ.TrivAt l.M → (actLat h Λ).TrivAt l.M → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (_ : AnFib X bas idx e x L y), x ∈ X.dom → SelfD X L → ∀ (wq wq' : (Fin n → LevQ Dw l) → c.F), (∀ q q', LevMoves h q q' → wq' q' = wq q) → ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (b b' : c.F) (v v' : ℂ), b ≠ 0 → b' ≠ 0 → ShortValAt Xo c nab wq Λ b N P y v → ShortValAt Xo c nab wq' (actLat h Λ) b' N' (pushLet c h P) y v' → ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) ≠ 0 ∧ v' * algebraMap c.F ℂ b' * (Real.sqrt (((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) = t * algebraMap c.F ℂ b * (Real.sqrt (((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) * v := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'
  have hw := cmHost_idempotent_trace_eq_one H
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨hU', hmv, hu, -⟩ := (GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ
  have hΛ := mem_vset Λ l.three_le hU hT
  have hΛ' := mem_vset (actLat h Λ) l.three_le (hU' hU) hT'
  have hΛ1 : Λ.La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ
  have hΛ1' : (actLat h Λ).La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'
  obtain ⟨t, ht, hvac⟩ := thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv
  refine ⟨t, ht, fun x L y A hx hL => ?_⟩
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)
  have hcol := hvac L hL v₀ hv₀ x hx
  intro wq wq' hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'
  obtain ⟨θ, hθ, -⟩ := (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1
  have hθ1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1
  obtain ⟨mk, hmk, hA⟩ := exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hroots := (DualMark.dual_marking E H Dw l r X L mk _ hL hmk
    (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n
  obtain ⟨Y, hY⟩ := hroots N hN.1.pos
  obtain ⟨Y', hY'⟩ := hroots N' hN'.1.pos
  have e1 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv
  have e2 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _
    ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n a h hh).1 P hP) wq' b' v' hv'
  obtain ⟨_, -, hproj⟩ := GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀
  obtain ⟨hu1, -, hp1⟩ := hproj _ hΛ1
  obtain ⟨hu2, -, hp2⟩ := hproj _ hΛ1'
  obtain ⟨⟨σ, hσ⟩, hmove⟩ := GlobalTheory.T.roots_levelPoints_same_vacuum_translates E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN'
    Y Y' hY hY'
  obtain ⟨-, -, -, hz1, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1
    (hN.2.2.trans inf_le_left)
  obtain ⟨-, -, -, hz2, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1
    (hN'.2.2.trans inf_le_left)
  haveI := finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  generalize unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1
  generalize unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2
  rw [gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1] at e1
  rw [gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1] at e2
  have hsum : ∑ q, algebraMap c.F ℂ (wq' q) * thP X hr bas idx (heisG X bas (Y' q) u')
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x =
      t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u)
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
    rw [← σ.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsb := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1
    have hsb' := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1
    have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx
    rw [hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP,
      GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,
      funext (thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),
      mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]
    rfl
  rw [hsum] at e2
  simp only [map_mul, map_inv₀, map_natCast] at e1 e2
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'
  refine ⟨?_, ?_⟩
  · rw [index_Ln, ← hrr]
    exact (Nat.pos_of_mul_pos_left (lt_of_lt_of_eq hz2 (zCard_eq _ hN' r))).ne'
  rw [index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v,
    _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]
  ring

end GlobalTheory.Phase.ChangePt

namespace GlobalTheory.DatumMove

theorem move_complex (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ]
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (hfib : ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
      (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)),
      IsSympl X bas ∧ r = Dw.p + Dw.q ∧
      (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧
      (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) ∧
      ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r),
        FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀))
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (w w' : (Fin n → LevQ Dw l) → c.F)
    (hw : ∀ q q', LevMoves h q q' → w' q' = w q) (N N' : ℕ) (hN : Λ.LevOK N l.M)
    (hN' : (actLat h Λ).LevOK N' l.M) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hPa : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    ∃ z : ℂ, ∀ (y : FrPt Xo c ℂ) (v v' : ℂ), ShortValAt Xo c nab w Λ 1 N P y v →
        ShortValAt Xo c nab w' (actLat h Λ) 1 N' (pushLet c h P) y v' → v = z * v' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  obtain ⟨r, g, X, bas, idx, e, hr, eL, hS, hr', hL, hrow, hy⟩ := hfib
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨t, ht1, ht⟩ := GlobalTheory.Phase.ChangePt.move_at_point hC E H Dw l Xo c r g X bas idx e Dw.p n hr eL hS hr' hn hL
    hrow nab hnab Λ h hU hh hT hT'
  have hP := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1 P hPa
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  set A := ((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) with hAdef
  set A' := ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q)
    with hA'def
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht1
  refine ⟨((Real.sqrt (A : ℝ) : ℝ) : ℂ) / (t * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ)), fun y v v' hv hv' => ?_⟩
  obtain ⟨y₀, t₀, x, L, hB, hx, hSD, ⟨F⟩⟩ := hy y
  have ex1 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa
    w 1).1 ℂ
  have ex2 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN'
    a _ hP w' 1).1 ℂ
  obtain ⟨u, hu, -⟩ := ex1 y₀
  obtain ⟨u', hu', -⟩ := ex2 y₀
  have k1 := (ex1 y).unique hv
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a P).2 hPa w Λ 1 N u hu)
  have k2 := (ex2 y).unique hv'
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a _).2 hP w' _ 1 N' u' hu')
  obtain ⟨hA', k3⟩ := ht x L y₀ F hx hSD w w' hw N N' hN hN' a P hPa 1 1 u u' one_ne_zero one_ne_zero hu hu'
  have hsq : ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA'))).ne'
  have k4 : u = ((Real.sqrt (A : ℝ) : ℝ) : ℂ) / (t * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ)) * u' := by
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ht0 hsq)]
    simp only [map_one, _root_.mul_one] at k3
    linear_combination -k3
  rw [k1, k2, k4]; ring

theorem exists_move_const (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l)
    [StarRing (𝓞 E)] (nab : NabV Xo c) (h1 : 1 ≤ Dw.p + Dw.q) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (w w' : (Fin n → LevQ Dw l) → c.F)
    (hw : ∀ q q', LevMoves h q q' → w' q' = w q) (N N' : ℕ) (hN : Λ.LevOK N l.M)
    (hN' : (actLat h Λ).LevOK N' l.M) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hPa : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    ∃ z : c.F, ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S),
      ShortValAt Xo c nab w Λ 1 N P y v →
        ∃ v', ShortValAt Xo c nab w' (actLat h Λ) 1 N' (pushLet c h P) y v' ∧ v = algebraMap c.F S z * v' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨s, hfib⟩ := GlobalTheory.Dict.exists_anFib_all_points E H Dw l Xo c h1 n hn
  obtain ⟨z, hid⟩ := @move_complex E _ _ _ H Dw l Xo c s.toAlgebra _ nab hnab n hn hfib
    Λ h hU hh hT hT' w w' hw N N' hN hN' a P hPa
  have hP := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1 P hPa
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  have ex1 := GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa w 1
  have ex2 := GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN'
    a _ hP w' 1
  choose u hu using fun (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => (ex1.1 S y).exists
  choose u' hu' using fun (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => (ex2.1 S y).exists
  have n1 : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (y' : FrPt Xo c T), FrMap φ y y' → φ (u S y) = u T y' :=
    fun S T _ _ _ _ φ y y' hy => ex1.2 S T φ y y' hy _ _ (hu S y) (hu T y')
  have n2 : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (y' : FrPt Xo c T), FrMap φ y y' → φ (u' S y) = u' T y' :=
    fun S T _ _ _ _ φ y y' hy => ex2.2 S T φ y y' hy _ _ (hu' S y) (hu' T y')
  have h : ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra,
      @u ℂ _ s.toAlgebra y = z * @u' ℂ _ s.toAlgebra y :=
    fun y => hid y _ _ (@hu ℂ _ s.toAlgebra y) (@hu' ℂ _ s.toAlgebra y)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : c.F, ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra,
      @u ℂ _ s.toAlgebra y = s z₀ * @u' ℂ _ s.toAlgebra y := by
    by_cases h0 : ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra, @u' ℂ _ s.toAlgebra y = 0
    · refine ⟨1, fun y => ?_⟩
      rw [h y, h0 y, mul_zero, mul_zero]
    · simp only [not_forall] at h0
      obtain ⟨y, hy⟩ := h0
      obtain ⟨z₀, hz₀⟩ := @GlobalTheory.ConstRatio.ratio_mem_range E _ _ _ H Dw l Xo c ℂ _ _ s.toAlgebra
        (@u' ℂ _ s.toAlgebra) (@u ℂ _ s.toAlgebra)
        (@n2 ℂ ℂ _ s.toAlgebra _ s.toAlgebra) (@n1 ℂ ℂ _ s.toAlgebra _ s.toAlgebra) z h y hy
      have hz₀' : s z₀ = z := hz₀
      exact ⟨z₀, fun y => by rw [hz₀', h y]⟩
  have hfin := GlobalTheory.NaturalValues.eq_of_eq_complex E H Dw l Xo c s u (fun S _ _ y => algebraMap c.F S z₀ * u' S y) n1
    (fun S T _ _ _ _ φ y y' hyy => by rw [map_mul, φ.commutes, n2 S T φ y y' hyy]) hz₀
  refine ⟨z₀, fun S _ _ y v hv => ⟨u' S y, hu' S y, ?_⟩⟩
  rw [(ex1.1 S y).unique hv (hu S y)]
  exact hfin S y

end GlobalTheory.DatumMove

end Point

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DatumMove

set_option maxHeartbeats 1000000 in

theorem rawSeries_move_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsNab Xo c nab → ∀ (bad n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → ∀ x0 x1 : Fin n → LevQc Dw l, Submodule.span (𝓞 E) (Set.range x0) = ⊤ → Submodule.span (𝓞 E) (Set.range x1) = ⊤ → {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)} ⊆ (Submodule.span c.F {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x1)) La N P y (f p y)} : Set (Formalism.L2.Pj.Rul Xo c)) := by
  intro E _ _ _ H Dw l Xo c _ nab h1 _ hnab bad n a hbad hdom x0 x1 hx0 hx1 f ⟨hf, Λ, N, P, hU, hT, hM, hN, hP, hv⟩
  obtain ⟨γ, hγ, hb, hm, hw⟩ := exists_unitary_moving c (bad := 2 * bad) (by omega) x0 x1 hx0 hx1
  have triv : ∀ d, d ∣ 2 * bad → (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ ⟨stdLat E n⟩).TrivAt d := fun d hd => by
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk.coprime_dvd_right hd, h⟩
  obtain ⟨N', hN'⟩ := exists_levOK (triv 2 (Dvd.intro _ rfl)) hN
  have hM' := trivAt_act hm hM
  obtain ⟨z, hz⟩ := exists_move_const E H Dw l Xo c nab h1 hnab n hdom.2 Λ γ hU hγ hM hM' _ _ hw N N' hN hN' a P hP.1
  obtain ⟨k1, -, -, k2⟩ := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a γ hγ).2 Λ
  by_cases hz0 : z = 0
  · have : f = 0 := by
      funext p y
      obtain ⟨v', -, e⟩ := hz p.R y _ (hv p y)
      rw [e, hz0, map_zero, zero_mul]
      rfl
    rw [this]
    exact Submodule.zero_mem _
  · have e : f = z • z⁻¹ • f := by
      funext p y
      change f p y = z • z⁻¹ • f p y
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hz0, map_one, one_mul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Submodule.smul_mem _ _ hf, _, N', _, k1 hU,
      trivAt_act (triv bad (Dvd.intro_left _ rfl)) hT, hM', hN', k2 P hP, fun p y => ?_⟩)
    obtain ⟨v', hv', e⟩ := hz p.R y _ (hv p y)
    have e2 : (z⁻¹ • f) p y = v' := by
      change z⁻¹ • f p y = v'
      rw [e, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_mul]
    rw [e2]
    exact hv'

end GlobalTheory.DatumMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPolynomialVectorReachedByRealDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigNZ.DatReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

section Tens

variable (W : G.Weil) {X Y : Node} {p : Path T X Y}

theorem tensT_zero (τ : TotT G p) : tensT W (0 : PolT G p →₀ ℂ) τ = 0 := Finsupp.sum_zero_index

theorem tensT_add (a b : PolT G p →₀ ℂ) (τ : TotT G p) : tensT W (a + b) τ = tensT W a τ + tensT W b τ := by
  unfold tensT
  refine Finsupp.sum_add_index' (fun P => by simp) (fun P c₁ c₂ => ?_)
  simp only [add_mul, Finsupp.single_add, Finsupp.sum_add]

theorem tensT_smul (c : ℂ) (a : PolT G p →₀ ℂ) (τ : TotT G p) : tensT W (c • a) τ = c • tensT W a τ := by
  unfold tensT
  rw [Finsupp.sum_smul_index' (fun P => by simp), Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only
  rw [Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem fock_one (q : Pair T) (f : WO (G.pS q) (G.pT q) → ℂ) : W.fock q f 1 = f := by
  unfold GridData.Weil.fock pureTensorO pureTensorL
  rw [show (1 : MvPolynomial (FVar D (G.pT q).rank (G.pS q).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 by
    rw [MvPolynomial.coe_basisMonomials]; rfl, Module.Basis.constr_basis]
  simp [opPow]

end Tens

section Datum

variable {t : T} {i j : ℕ} (W : G.Weil) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)

noncomputable def onePol : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) := (((), 1), 1)

theorem tensT_one (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) : tensT W (Finsupp.single onePol 1) τ = τ := by
  unfold tensT
  rw [Finsupp.sum_single_index (by simp)]
  have hz : ∀ d : PureT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j), Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d onePol = d := by
    rintro ⟨⟨⟨⟩, d₁⟩, d₂⟩
    show (((), W.fock _ d₁ 1), W.fock _ d₂ 1) = (((), d₁), d₂)
    rw [fock_one, fock_one]
  simp only [hz, one_mul]
  exact Finsupp.sum_single τ

theorem isDatumA_zero : IsDatumA W e Γ (0 : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) 0 := by
  refine ⟨Submodule.zero_mem _, fun u => ?_⟩
  have : Γ.M.co.rho W.ψ u 0 = 0 := by
    funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  rw [this, Finsupp.sum_zero_index]
  simp [GlobalTheory.WeilM.thetaSum]

theorem datumA_add (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ) {τ τ' : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)} {Φ Φ'} (h : IsDatumA W e Γ τ Φ)
    (h' : IsDatumA W e Γ τ' Φ') : IsDatumA W e Γ (τ + τ') (Φ + Φ') := by
  refine ⟨add_mem h.1 h'.1, fun u => ?_⟩
  have e1 : Γ.M.co.rho W.ψ u (Φ + Φ') = Γ.M.co.rho W.ψ u Φ + Γ.M.co.rho W.ψ u Φ' := by
    funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]; ring
  rw [e1, GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA _ _ hψ _ _ h.1) (GlobalTheory.HeisSchA.rho_mem_schA _ _ hψ _ _ h'.1),
    h.2, h'.2, Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem datumA_smul (c : ℂ) {τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)} {Φ} (h : IsDatumA W e Γ τ Φ) :
    IsDatumA W e Γ (c • τ) (c • Φ) := by
  refine ⟨Submodule.smul_mem _ c h.1, fun u => ?_⟩
  have e1 : Γ.M.co.rho W.ψ u (c • Φ) = c • Γ.M.co.rho W.ψ u Φ := by
    funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, GlobalTheory.WeilM.thetaSum_smul, h.2, Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  simp only [smul_eq_mul, mul_assoc]

end Datum

section Pure

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)

theorem pure_zero : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf F κ) φ = 0 := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]

theorem pure_add (f f' : SInf F κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + f') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul (c : ℂ) (f : SInf F κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end Pure

theorem datum_real : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ f₀, f₀ ≠ 0 → Γ.M.IsGauss Bs.ψ Bs.emb f₀ → IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∃ a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f₀ hf₀ hG hD
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  change TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) at τ
  let N : Submodule ℂ (SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) :=
    { carrier := {f | ∃ a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)}
      zero_mem' := ⟨0, by rw [tensT_zero, pure_zero]; exact isDatumA_zero W e Γ⟩
      add_mem' := by
        rintro f f' ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', by rw [tensT_add, pure_add]; exact datumA_add W e Γ hψ ha ha'⟩
      smul_mem' := by
        rintro c f ⟨a, ha⟩
        exact ⟨c • a, by rw [tensT_smul, pure_smul]; exact datumA_smul W e Γ c ha⟩ }
  have h0 : f₀ ∈ N := ⟨Finsupp.single onePol 1, by rw [tensT_one]; exact hD⟩
  have hle : Γ.M.Pol Bs.ψ Bs.emb ≤ N := sInf_le ⟨fun g hg => by
      obtain ⟨c, rfl⟩ := GlobalTheory.T.fockVacua_triple_proportional_to_nonzero Bs Γ X om om' hT f₀ hf₀ hG g hg
      exact N.smul_mem c h0,
    fun u hu f ⟨a, ha⟩ f₁ h1 => GlobalTheory.T.archimedeanSchwartzDatum_stable_heisenbergDerivative hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f a ha u hu f₁ h1⟩
  exact fun f hf => hle hf

end GlobalTheory.BigNZ.DatReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∀ p, ∀ l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ, l ∘ₗ om p ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ := by
  first | exact @GlobalTheory.WeilAdm.transport_adm | exact GlobalTheory.WeilAdm.transport_adm | (intros; apply GlobalTheory.WeilAdm.transport_adm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSchwartzSurjective
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.ThetaChange

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c₀ * thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij
  have hstd : IsStd B.ψ := hP.base.std
  have hrk : Module.finrank F E = 2 := hP.base.cm.2.2.1
  obtain ⟨Φr, hΦr⟩ := GlobalTheory.RatCoord.ratEquiv F E σ n d X W M B.ψ hP.good hrk
  obtain ⟨lθ, hlθ, hlθ'⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  have hcomp := GlobalTheory.EvAdm.comp_mem_adm F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE lθ hlθ
  have hinc1 : ∀ k : ℕ, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := by
    intro k; unfold incM; exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨c, hc⟩ := GlobalTheory.T.schwartz_functional_archimedean_factor F B.ψ hstd (Fin n × Fin d) (fun Φ => thetaSum F (e Φ))
    (fun Φ hΦ Ψ hΨ => by
      simp only [map_add]
      exact GlobalTheory.WeilM.thetaSum_add F (hE.maps Φ hΦ) (hE.maps Ψ hΨ))
    (fun c Φ _ => by simp only [map_smul]; exact GlobalTheory.WeilM.thetaSum_smul F c (e Φ))
    (fun g hg => by
      obtain ⟨T, hT⟩ := hcomp g hg
      refine ⟨T, fun f => ?_⟩
      have hm : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
      rw [← hlθ' _ (hE.maps _ hm)]
      exact hT f)
    (fun a b Φ hΦ => by
      set x := Φr.symm (a, b) with hx
      have hxe : M.co.e (incM F x) = ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) := by
        rw [hΦr x, hx, LinearEquiv.apply_symm_apply]
      have h1 : schr B.ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ =
          M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F x * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ := by
        rw [hinc1, hinc1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
        show _ = schr B.ψ (M.co.e (incM F x)) Φ
        rw [hxe]
      rw [h1, hE.Heisenberg₂ _ Φ hΦ]
      obtain ⟨y, z, hyz⟩ := hM₁.rat x
      show thetaSum F (schr B.ψ (M₁.co.e (incM F x)) (e Φ)) = _
      rw [hyz]
      exact GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ (fun a => hstd.2.1 a) y z (e Φ))
  refine ⟨c, ?_, hc⟩
  rintro rfl
  obtain ⟨φ₀, hφ₀, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
  obtain ⟨Φ, hΦ, rfl⟩ := hbij.surjOn hφ₀
  exact hne (by rw [hc Φ hΦ, zero_mul])

end GlobalTheory.ThetaChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilModelLineActionExistsStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_line_action_exists : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ : SInf F (Fin n × Fin d),
      GlobalTheory.RealLift.SD (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ := by
  first | exact @GlobalTheory.RealLift.FirstLine.sd_exists | exact GlobalTheory.RealLift.FirstLine.sd_exists | (intros; apply GlobalTheory.RealLift.FirstLine.sd_exists <;> assumption)
end

