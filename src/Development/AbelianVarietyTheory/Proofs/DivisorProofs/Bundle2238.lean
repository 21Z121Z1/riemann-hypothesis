import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundedOddInertPrimeCmType
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem inPsi_orbit_parity {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {h : ℕ}
    (hh : 0 < h) (lab : ZMod h → (E →+* ℂ)) (hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s))
    (h0 : InPsi H (lab 0)) : Even h ∧ ∀ s : ZMod h, InPsi H (lab s) ↔ Even s.val := by
  have hn : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) ↔ Even n := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [Nat.cast_succ, hstep, ih, Nat.even_add_one]
  haveI : NeZero h := ⟨hh.ne'⟩
  refine ⟨(hn h).1 (by simpa [ZMod.natCast_self] using h0), fun s => ?_⟩
  have := hn s.val
  rwa [ZMod.natCast_zmod_val] at this

theorem facBetween_fine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → 1 ≤ k → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundFine p (Dw.p + Dw.q) Dw.q (rk f) k := by
  intro E _ _ _ H Dw l Xo c p _ la hp2 hdisc hin f k hf hk
  letI := H.starRing
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hL : 0 ≤ Real.logb p k := Real.logb_nonneg hp1 (by exact_mod_cast hk)
  refine ⟨((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1),
    k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)), ?_, ?_⟩
  · intro T io e ho y
    refine ⟨le_nuFac fun Ch X => ?_, fun halg =>
      (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) halg hp2 hdisc f k hf).2 hin⟩
    obtain ⟨hfrob, hty⟩ := GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks E H Dw l Xo c (fun _ => rfl) p hdisc T io X
    obtain ⟨h, hh0, -, lab, horb, d', G', ty, I, P, -, ⟨mu⟩, -, hcard, hfr⟩ := hty y Ch f.1
    have hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s) := by
      intro s
      rw [((hfrob _ _ (horb.2.1 s)).2 hin)]
      constructor
      · intro h1 h2
        exact ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both H (lab s) ⟨h2, h1⟩
      · intro h1
        exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H (lab s)).resolve_left h1
    obtain ⟨hev, hpar⟩ := inPsi_orbit_parity hh0 lab hstep (by rw [horb.1]; exact hf)
    have hodd : ∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ Dw.q := by
      intro s hs
      have hn : ¬ InPsi H (lab s) := fun h1 => (Nat.not_even_iff_odd.2 hs) ((hpar s).1 h1)
      have h2 := hcard s
      rw [if_neg hn] at h2
      rw [← h2, Fintype.card_subtype]
    obtain ⟨hsat, hzero, hdep⟩ := hfr 0 f horb.1.symm
    obtain ⟨cr, -, hcr, hlow⟩ := GlobalTheory.T.detDepth_lower_bound_saturated_even_type X.C (vX_vp X) p hp (vX_vp_p X) hp3 d' h hh0 hev ty G' mu Dw.q hodd
      (0 : ZMod h) (by simp) (rk f) k hk (fun a => P.mulVec (frame Ch X f a)) hsat hzero
    rw [nuFacC, ← hdep] at *
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hlow
    have h3 : ((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p ≤ ((rk f : ℝ) - cr) * k * p := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h4 := div_le_div_of_nonneg_right h3 hpp.le
    linarith
  · have hab : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 1 / ((p : ℝ) - 1) := by
      rw [div_le_div_iff₀ hpp (by linarith)]
      nlinarith
    have hkey : boundFine p (Dw.p + Dw.q) Dw.q (rk f) k -
        (k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) -
          (((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1))) =
        (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      unfold boundFine
      push_cast
      ring
    have hpos : 0 ≤ (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      have hb : 0 ≤ 1 / ((p : ℝ) - 1) := by apply div_nonneg <;> linarith
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 3 / 2 + Real.logb p k / 2) (sub_nonneg.2 hab)
      positivity
    linarith

end GlobalTheory.RefSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyMemberTangentValueEqFirstJet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetF

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}}

def vH (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valF_eq (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) : valF x U a = vH x U h a := by
  rw [valF, dif_pos h]; rfl

theorem valF_appLE {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_res {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_unit_ne (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) : valF x U a.val ≠ 0 := by
  rw [valF_eq x U h]
  exact (a.isUnit.map _).ne_zero

variable {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem mem_wchart {r : Sp F ⟶ Y} {j : K → L.ι} :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (r ≫ φ k) ⁻¹ᵁ L.U (j k) :=
  ⟨fun h k _ hq => Set.mem_iInter.1 (h hq) k, fun h _ hq => Set.mem_iInter.2 fun k => h k hq⟩

theorem valF_sec (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j) (h' : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j') :
    valF r (LB.wchart L φ j) (s.f j) =
      (∏ k, valF (r ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valF r (LB.wchart L φ j') (s.f j') := by
  have h2 : ⊤ ≤ r ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have c := congrArg (vH r (LB.wchart L φ j ⊓ LB.wchart L φ j') h2) (s.compat j j')
  erw [map_mul] at c
  refine (valF_res inf_le_left h2 _).symm.trans ((valF_eq _ _ h2 _).trans (c.trans (congrArg₂ (· * ·) ?_
    ((valF_eq _ _ h2 _).symm.trans (valF_res inf_le_right h2 _)))))
  let ψ : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ →* F :=
    (vH r (LB.wchart L φ j ⊓ LB.wchart L φ j') h2).toMonoidHom.comp (Units.coeHom _)
  change ψ (∏ k, _) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  change (Units.coeHom F) ((Units.map (vH r (LB.wchart L φ j ⊓ LB.wchart L φ j') h2).toMonoidHom) _) = _
  rw [map_zpow, map_zpow]
  congr 1
  rw [← valF_appLE (φ k) _ (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
      (inf_le_right.trans (LB.wchart_le L φ j' k))) h2, valF_eq _ _ h2]
  rfl

end Val

section Jet
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def jet (W : E) (f : E → ℂ) (x : E) : DualNumber ℂ :=
  TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (fderiv ℂ f x W)

theorem jet_mul (W : E) {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x) :
    jet W (fun z => f z * g z) x = jet W f x * jet W g x := by
  unfold jet
  rw [fderiv_fun_mul hf hg]
  ext <;> simp <;> ring

theorem jet_const (W : E) (c : ℂ) (x : E) : jet W (fun _ => c) x = TrivSqZeroExt.inl c := by
  simp [jet]

theorem jet_pow (W : E) {f : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x) (k : ℕ) :
    jet W (fun z => f z ^ k) x = jet W f x ^ k := by
  induction k with
  | zero => simp [jet_const]
  | succ k ih =>
    simp only [pow_succ]
    rw [jet_mul W (hf.fun_pow k) hf, ih]

theorem jet_congr (W : E) {f g : E → ℂ} {x : E} (h : f =ᶠ[nhds x] g) : jet W f x = jet W g x := by
  unfold jet
  rw [h.fderiv_eq, h.eq_of_nhds]

theorem jet_add (W : E) (f : E → ℂ) (c : E) : jet W (fun z => f (c + z)) 0 = jet W f c := by
  unfold jet
  rw [fderiv_comp_add_left]
  simp only [add_zero]

end Jet

section Main
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
  (ν : NumOf D ℂ N) (d : AB N.toNumB g)

theorem ex_zero : d.ex 0 = 1 := by
  have := d.ex_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem ptB_prB (z : Fin g → ℂ) : ptB ν d z ≫ (DegPre.prB D ℂ).left = (ν.eA (d.ex z)).left :=
  congrArg (·.left) (lift_snd (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)))

theorem ptB_fam {α : N.X} {ct : Fin g → ℂ} (hc : N.c α = d.ex ct) (z : Fin g → ℂ) (k : Fin 4) :
    ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) k = (ν.eA (d.ex (![z, ct + z, ct, 0] k))).left := by
  have e2 : lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) ≫ toUnit _ ≫ D.c (ν.eX α) = ν.eA (d.ex ct) := by
    rw [← hc, ν.c_eq, ← Category.assoc, comp_toUnit]
  fin_cases k
  · exact ptB_prB ν d z
  · refine congrArg (·.left) (?_ : lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) ≫
      (DegPre.prB D ℂ * (toUnit _ ≫ D.c (ν.eX α))) = ν.eA (d.ex (ct + z)))
    rw [MonObj.comp_mul, e2, lift_snd, add_comm, d.ex_add, map_mul]
  · exact congrArg (·.left) e2
  · refine congrArg (·.left) (?_ : lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) ≫
      toUnit _ ≫ η[D.P.A] = ν.eA (d.ex 0))
    rw [ex_zero, map_one, ← Category.assoc, comp_toUnit]
    rfl

variable {ν d}

theorem open_chart (G : Geo ν d) (i : D.P.L.ι) : IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i} := by
  have := (G.hol ((DegPre.prB D ℂ).left ⁻¹ᵁ D.P.L.U i) 0).1
  simp only [← ptB_prB]
  exact this

theorem frG_diff (G : Geo ν d) (x : Fin g → ℂ) : DifferentiableAt ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x :=
  (G.fr_hol _).differentiableAt ((open_chart G _).mem_nhds (ν.good _))

theorem val_fam (G : Geo ν d) {k : ℕ} {s : Fam D ℂ k} {f : N.X → N.A → ℂ} {α : N.X} {ct : Fin g → ℂ} {φ : (Fin g → ℂ) → ℂ}
    (hs : ν.FamV s f) (hc : N.c α = d.ex ct)
    (hφ : ∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z))
    (j : Fin 4 → D.P.L.ι) (z : Fin g → ℂ) (h : ⊤ ≤ ptB ν d z ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j) :
    valF (ptB ν d z) (LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j) ((s.s (ν.eX α)).f j) * G.frG (j 2) ct * G.frG (j 0) z =
      φ z * G.frG (j 0) z ^ k * G.frG (j 1) (ct + z) * G.frG (j 3) 0 := by
  have h' : ⊤ ≤ ptB ν d z ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α))
      (fun k => ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) k)) := mem_wchart.2 fun _ => ν.good _
  have e := valF_sec (s.s (ν.eX α)) (ptB ν d z) j _ h h'
  have e' : valF (ptB ν d z) _ ((s.s (ν.eX α)).f (fun k => ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) k))) =
    f α (d.ex z) * ν.rg ^ k := (hs α (d.ex z)).symm
  have key : ∀ l : Fin 4, ∃ u : ℂ, u ≠ 0 ∧ valF (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) l)
      (D.P.L.U (j l) ⊓ D.P.L.U (ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) l)))
      (D.P.L.g (j l) (ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) l))).val = u ∧
      G.frG (j l) (![z, ct + z, ct, 0] l) = u * (d.fr (![z, ct + z, ct, 0] l) * ν.rg) := fun l => by
    have h1 := mem_wchart.1 h l
    rw [ptB_fam ν d hc] at h1 ⊢
    have h2 : ⊤ ≤ (ν.eA (d.ex (![z, ct + z, ct, 0] l))).left ⁻¹ᵁ
        (D.P.L.U (j l) ⊓ D.P.L.U (ν.J (ν.eA (d.ex (![z, ct + z, ct, 0] l))).left)) :=
      fun q hq => ⟨h1 hq, ν.good _ hq⟩
    exact ⟨_, valF_unit_ne _ _ h2 _, rfl, by rw [G.fr_compat _ _ _ h2, G.fr_eq]⟩
  choose u hu0 hu1 hu2 using key
  have e3 := e.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun l _ => congrArg (· ^ DegPre.famε k l) (hu1 l)) e')
  rw [e3, Fin.prod_univ_four]
  have a0 : G.frG (j 0) z = u 0 * (d.fr z * ν.rg) := hu2 0
  have a1 : G.frG (j 1) (ct + z) = u 1 * (d.fr (ct + z) * ν.rg) := hu2 1
  have a2 : G.frG (j 2) ct = u 2 * (d.fr ct * ν.rg) := hu2 2
  have a3 : G.frG (j 3) 0 = u 3 * (d.fr 0 * ν.rg) := hu2 3
  rw [a0, a1, a2, a3, d.fr_zero]
  change u 0 ^ ((k : ℤ) - 1) * u 1 ^ (1 : ℤ) * u 2 ^ (-1 : ℤ) * u 3 ^ (1 : ℤ) * _ * _ * _ = _
  rw [zpow_sub₀ (hu0 0), zpow_natCast]
  simp only [zpow_one, _root_.zpow_neg, Units.val_one, mul_pow]
  rw [div_eq_mul_inv]
  linear_combination (u 0 ^ k * u 1 * u 3 * ν.rg ^ k * ν.rg ^ 2) * hφ z +
    (u 0 ^ k * u 1 * u 3 * ν.rg ^ k * ν.rg ^ 2) * (f α (d.ex z) * d.fr ct * d.fr z) *
      (u 2 * (u 2)⁻¹ * mul_inv_cancel₀ (hu0 0) + mul_inv_cancel₀ (hu0 2))

theorem red_eq (b : TE R ℂ ⟶ D.P.A) (hb : redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left) :
    redE ℂ ≫ (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left = ptB ν d 0 := by
  have h0 : redE ℂ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
  let ρ : TF (R := R) ℂ ⟶ TE R ℂ := Over.homMk (redE ℂ) (by
    change redE ℂ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ _ = _
    rw [← Category.assoc, h0, Category.id_comp])
  refine congrArg (·.left) (?_ : ρ ≫ lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b =
    lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)))
  rw [comp_lift, ex_zero, map_one]
  congr 1
  · exact Over.OverMorphism.ext h0
  · exact Over.OverMorphism.ext hb

end Main

end GlobalTheory.MBLow.Cl.JetF

namespace GlobalTheory.MBLow.Cl
open JetF

theorem sE_fam_eq_jet : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g) (G : Geo ν d) (b : TE R ℂ ⟶ D.P.A) (W : Fin g → ℂ), redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → IsD ν d W b → ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (ct : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ), ν.FamV s f → N.c α = d.ex ct → Differentiable ℂ φ → (∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z)) → sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) = (TrivSqZeroExt.inl (φ 0) + TrivSqZeroExt.inr (fderiv ℂ φ 0 W)) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) ^ k * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) := by
  intro R _ _ _ _ D _ _ _ N ν g d G b W hb hD k s f α ct φ hs hc hφ hf
  let j : Fin 4 → D.P.L.ι := fun l => ν.J (ptB ν d 0 ≫ DegPre.famφ D ℂ (ν.eX α) l)
  have hU : ⊤ ≤ ptB ν d 0 ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j := mem_wchart.2 fun _ => ν.good _
  have j0 : j 0 = ν.J (ν.eA (d.ex 0)).left := congrArg ν.J (ptB_fam ν d hc 0 0)
  have j1 : j 1 = ν.J (ν.eA (d.ex ct)).left := congrArg ν.J ((ptB_fam ν d hc 0 1).trans (by simp))
  have j2 : j 2 = ν.J (ν.eA (d.ex ct)).left := congrArg ν.J (ptB_fam ν d hc 0 2)
  have j3 : j 3 = ν.J (ν.eA (d.ex 0)).left := congrArg ν.J (ptB_fam ν d hc 0 3)
  let h : (Fin g → ℂ) → ℂ := fun z =>
    valF (ptB ν d z) (LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j) ((s.s (ν.eX α)).f j)
  have e1 : sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl :
      TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J = jet W h 0 := by
    have ej : (fun l => ν.J (redE ℂ ≫ (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl :
        TE R ℂ ⟶ TF (R := R) ℂ) b).left ≫ DegPre.famφ D ℂ (ν.eX α) l)) = j := funext fun l =>
      congrArg ν.J ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (red_eq b hb)))
    unfold sE
    rw [ej]
    exact hD _ _ hU
  obtain ⟨ho, hd⟩ := G.hol _ ((s.s (ν.eX α)).f j)
  have hn := ho.mem_nhds hU
  have hh : DifferentiableAt ℂ h 0 := hd.differentiableAt hn
  have d0 := frG_diff G 0
  have dc : DifferentiableAt ℂ (fun z => G.frG (ν.J (ν.eA (d.ex ct)).left) (ct + z)) 0 := by
    refine DifferentiableAt.comp (g := G.frG (ν.J (ν.eA (d.ex ct)).left)) (f := fun z => ct + z) 0 ?_ (by fun_prop)
    rw [add_zero]
    exact frG_diff G ct
  have ev : (fun z => h z * G.frG (ν.J (ν.eA (d.ex ct)).left) ct * G.frG (ν.J (ν.eA (d.ex 0)).left) z) =ᶠ[nhds 0]
      fun z => φ z * G.frG (ν.J (ν.eA (d.ex 0)).left) z ^ k * G.frG (ν.J (ν.eA (d.ex ct)).left) (ct + z) *
        G.frG (ν.J (ν.eA (d.ex 0)).left) 0 := by
    filter_upwards [hn] with z hz
    have := val_fam G hs hc hf j z hz
    rwa [j0, j1, j2, j3] at this
  have := jet_congr W ev
  rw [jet_mul W (hh.mul_const _) d0, jet_mul W hh (differentiableAt_const _), jet_const,
    jet_mul W (((hφ 0).fun_mul (d0.fun_pow k)).fun_mul dc) (differentiableAt_const _), jet_const,
    jet_mul W ((hφ 0).fun_mul (d0.fun_pow k)) dc, jet_mul W (hφ 0) (d0.fun_pow k), jet_pow W d0, jet_add] at this
  rw [e1]
  exact this

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilySectionSpanPullbacksUnitBall
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing

noncomputable section
namespace GlobalTheory.SpanBall
open TWM TWO SectionScalarValuation

section Gen

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] (S : ValuationSubring F) (g : V →+* S)
  (hg : (algebraMap S F).comp g = algVF (F := F) (V := V))

abbrev TS : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom g))

abbrev ιT : TF (R := V) F ⟶ TS S g :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap S F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap S F)) ≫ Spec.map (CommRingCat.ofHom g) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

abbrev jT : DegPre.BF D.toPre F ⟶ TS S g ⊗ D.toPre.P.A := ιT S g hg ▷ D.toPre.P.A

theorem jT_snd : (jT S g hg (D := D)).left ≫ (snd (TS S g) D.toPre.P.A).left = (DegPre.prB D.toPre F).left := by
  rw [← Over.comp_left, whiskerRight_snd]

theorem jT_fst : (jT S g hg (D := D)).left ≫ (fst (TS S g) D.toPre.P.A).left =
    (fst (TF (R := V) F) D.toPre.P.A).left ≫ (ιT S g hg).left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

abbrev ιs (r : Γ(Spec (CommRingCat.of S), ⊤)) : F :=
  algebraMap S F ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom r)

theorem gs_jT {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (r : Γ(Spec (CommRingCat.of S), ⊤)) :
    gs (ρ ≫ (jT S g hg (D := D)).left) z ⊤ ((fst (TS S g) D.toPre.P.A).left.appTop.hom r) =
      gs ρ z ⊤ (gF D.toPre F (ιs S r)) := by
  have e1 : gs (ρ ≫ (jT S g hg (D := D)).left) z ⊤ ((fst (TS S g) D.toPre.P.A).left.appTop.hom r) =
      gs ((ρ ≫ (jT S g hg (D := D)).left) ≫ (fst (TS S g) D.toPre.P.A).left) z ⊤ r := gs_pull _ _ z ⊤ trivial r
  rw [e1, Category.assoc, jT_fst, ← Category.assoc]
  have e2 : gs ((ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ (ιT S g hg).left) z ⊤ r =
      gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤ ((ιT S g hg).left.appTop.hom r) :=
    (gs_pull _ _ z ⊤ trivial r).symm
  have e3 : gs ρ z ⊤ (gF D.toPre F (ιs S r)) = gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (ιs S r)) := gs_pull _ _ z ⊤ trivial _
  rw [e2, e3, show (ιT S g hg).left = Spec.map (CommRingCat.ofHom (algebraMap S F)) from rfl, appTop_specMap]
  rfl

theorem isPullback_jT : IsPullback (jT S g hg (D := D)).left (fst (TF (R := V) F) D.toPre.P.A).left
    (fst (TS S g) D.toPre.P.A).left (Spec.map (CommRingCat.ofHom (algebraMap S F))) := by
  have H₁ : IsPullback (snd (TS S g) D.toPre.P.A).left (fst (TS S g) D.toPre.P.A).left D.toPre.P.A.hom
      (TS S g).hom := (IsPullback.of_hasPullback (TS S g).hom D.toPre.P.A.hom).flip
  have H₀ : IsPullback (DegPre.prB D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left D.toPre.P.A.hom
      (TF (R := V) F).hom := (IsPullback.of_hasPullback (TF (R := V) F).hom D.toPre.P.A.hom).flip
  rw [← jT_snd S g hg, ← Over.w (ιT S g hg)] at H₀
  exact H₀.of_right (jT_fst S g hg) H₁

include hg in

theorem span_gen (hloc : IsLocalHom g) {k : ℕ} (hk : 1 ≤ k) {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) :
    ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.toPre.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (σF i) (D.toPre.famφB α)
        (DegPre.famε k) (σ i) (DegPre.prB D.toPre F).left 1) ∧
      ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre F (a i) _ * (σF i).f j := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have hp : IsProper (fst (TS S g) D.toPre.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TS S g).hom D.toPre.P.A.hom))
  have : CompactSpace (TS S g).left := inferInstanceAs (CompactSpace (Spec (CommRingCat.of S)))
  have : QuasiSeparatedSpace (TS S g).left := inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of S)))
  have : CompactSpace (TS S g ⊗ D.toPre.P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst (TS S g) D.toPre.P.A).left
  have : QuasiSeparatedSpace (TS S g ⊗ D.toPre.P.A).left :=
    (quasiSeparated_iff_quasiSeparatedSpace (fst (TS S g) D.toPre.P.A).left).mp inferInstance
  obtain ⟨s₁, hs₁⟩ := exists_sec hL (φ' := fun i => (jT S g hg (D := D)).left ≫
      (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α i) (ε' := DegPre.famε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      rw [GC.famφ_eq, ← jT_snd S g hg, Category.assoc]) s
  obtain ⟨t, ht, S₀, hS₀⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors S) (isPullback_jT S g hg (D := D)) hL
    (fun i => (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) s₁
  obtain ⟨n, rr, σ, hσ⟩ := GlobalTheory.TwistSpanExample.span_holds V D.toPre k hk α S g hloc S₀
  choose σF hσF using fun i => FamInt.exists_pull (D := D) (F := F) (σ i)
  have ht0 : (t : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := F) ht
  refine ⟨n, fun i => (t : F)⁻¹ * ιs S (rr i), σ, σF, hσF, fun j => ?_⟩
  refine (sec_ext_val hL (s' := FamInt.secLin (fun i => gF D.toPre F ((t : F)⁻¹ * ιs S (rr i))) σF)
    (fun y J hJ => ?_) j).trans rfl
  rw [sval_lin (s := FamInt.secLin _ _) (fun i => gF D.toPre F ((t : F)⁻¹ * ιs S (rr i))) σF (fun _ => rfl) _ y hJ]
  have e₁ : sval S₀ (𝟙 _ ≫ (jT S g hg (D := D)).left) y J = gs (𝟙 _) y ⊤ (gF D.toPre F t) * sval s (𝟙 _) y J := by
    rw [← hs₁ _ _ y J hJ, sval_of S₀ (𝟙 _ ≫ (jT S g hg (D := D)).left) y J (fun a => J (𝟙 _ ≫ (jT S g hg (D := D)).left ≫
      (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α a)) (fun a => by rw [Category.assoc])]
    refine (hS₀ _ (𝟙 _) y _ (hJ.mem (fun a => (jT S g hg (D := D)).left ≫
      (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
    have e := gs_jT S g hg (D := D) (𝟙 _) y ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom t)
    rw [show ιs S ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom t) = (t : F) by simp [ιs]] at e
    rw [← e, ← Category.assoc]
    exact (gs_pull _ _ y ⊤ trivial _).symm
  have e₂ := sval_lin (fun l => (fst (TS S g) D.toPre.P.A).left.appTop.hom (rr l))
      (fun l => pullSec D.toPre.P.L _ _ (σ l) (snd (TS S g) D.toPre.P.A).left) (fun j => hσ j)
      (𝟙 _ ≫ (jT S g hg).left) y hJ
  have g' : ∀ a b : F, gs (𝟙 _) y ⊤ (gF D.toPre F (a * b)) =
      gs (𝟙 _) y ⊤ (gF D.toPre F a) * gs (𝟙 _) y ⊤ (gF D.toPre F b) := fun a b => by
    rw [map_mul, gs_mul _ y ⊤ trivial]
  have g₁ : gs (𝟙 _) y ⊤ (gF D.toPre F (t : F)⁻¹) * gs (𝟙 _) y ⊤ (gF D.toPre F t) = 1 := by
    rw [← g', inv_mul_cancel₀ ht0, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]
  rw [← _root_.one_mul (sval s _ y J), ← g₁, _root_.mul_assoc, ← e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g', gs_jT, sval_pullSec _ _ _ _ _ y hJ, Category.assoc, jT_snd, secScal_sval (hσF i) _ y hJ, _root_.mul_assoc]

end Gen

theorem isLocalHom_ball {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing V) C]
    (hC : CExt V (maximalIdeal V) C) (S : ValuationSubring C) (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) :
    IsLocalHom ((algVF (F := C) (V := V)).codRestrict S.toSubring fun x => (hS _).2 (hC.1 x)) where
  map_nonunit x hx := by
    by_contra hxu
    have hm : x ∈ maximalIdeal V := (mem_maximalIdeal x).2 hxu
    have h1 : ‖algVF (F := C) (V := V) x‖ < 1 := hC.2 x hm
    obtain ⟨u, hu⟩ := hx
    have a1 : ‖((u : S) : C)‖ ≤ 1 := (hS _).1 (u : S).2
    have a2 : ‖(((u⁻¹ : Sˣ) : S) : C)‖ ≤ 1 := (hS _).1 ((u⁻¹ : Sˣ) : S).2
    have e : ((u : S) : C) * (((u⁻¹ : Sˣ) : S) : C) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
    have e' : ‖((u : S) : C)‖ * ‖(((u⁻¹ : Sˣ) : S) : C)‖ = 1 := by rw [← norm_mul, e, norm_one]
    have hux : ((u : S) : C) = algVF (F := C) (V := V) x := by rw [hu]; rfl
    rw [← hux] at h1
    nlinarith [mul_le_mul_of_nonneg_left a2 (norm_nonneg ((u : S) : C)), norm_nonneg (((u⁻¹ : Sˣ) : S) : C)]

theorem span_ball : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (S : ValuationSubring C), (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) → ∀ (k : ℕ), 1 ≤ k → ∀ (β : D.toPre.X) (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), ∃ (n : ℕ) (a : Fin n → C) (σ : Fin n → D.toPre.SecB k β) (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) (σF i) (D.toPre.famφB β) (DegPre.famε k) (σ i) (DegPre.prB D.toPre C).left 1) ∧ ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre C (a i) _ * (σF i).f j := by
  intro V _ _ _ D C _ _ hC S hS k hk β s
  exact span_gen (D := D) S _ rfl (isLocalHom_ball hC S hS) hk s

end GlobalTheory.SpanBall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowGramAlgebraicSectionStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.final_row_gram_algebraic_section : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∀ g : (p.F.lv2.lvl false).P, (∀ x : (p.T.Q.Dw ((i : ℕ) + 1)).La, (p.O i).lev (g : p.P.Gp) x - x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) → g = 1 := by
  first | exact @GlobalTheory.BaseLevelInj.eq_one_of_lev_cong | exact GlobalTheory.BaseLevelInj.eq_one_of_lev_cong | (intros; apply GlobalTheory.BaseLevelInj.eq_one_of_lev_cong <;> assumption)
end

