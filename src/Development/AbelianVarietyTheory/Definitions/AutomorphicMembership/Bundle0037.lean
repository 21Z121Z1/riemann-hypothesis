import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.ShFam.Descent GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Frame

variable (Z : Model Xo c β) {R : Type} [CommRing R] [Algebra c.F R] (P : FrPt Xo c R)

def frameOf : EigFrame Z (algebraMap c.F R) (GlobalTheory.AllWt.ptF P ≫ Z.j) := (exists_tie_frame P rfl).choose

theorem tie_frameOf : Comparison₂ P (frameOf Z P) := (exists_tie_frame P rfl).choose_spec

variable {Z P}

end Frame

variable {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem IsCoord.const_mul {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
    {n : Letter Dw → ℤ} {σ : Y.Y.Fn} {a : k} (h : IsCoord Y p g n σ a) (b : c.F) :
    IsCoord Y p g n (constF e Y.Y b * σ) (φ b * a) := by
  obtain ⟨y, ψ, φ₁, f, t, t', r, h1, h2, h3, h4, h5⟩ := h
  refine ⟨y, ψ, φ₁, f, t, t', φ₁ b * r, h1, h2, h3, ?_, ?_⟩
  · rw [map_mul, h4, mul_assoc]
    exact congrArg (· * _) (RingHom.congr_fun h2.2.1 b).symm
  · rw [map_mul, h5, mul_assoc, h3.2.1]
    rfl

theorem IsCoord.carries {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
    {n : Letter Dw → ℤ} {σ : Y.Y.Fn} {a : k} (h : IsCoord Y p g n σ a) : Y.Carries p g := by
  obtain ⟨y, ψ, φ₁, f, t, t', -, h1, h2, h3, -⟩ := h
  exact ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩

def CoordAt {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ p : Sp k ⟶ Y.Y.X, p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ ∧ IsCoord Y p (frameOf Z P) n σ a

def Carried {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) : Prop :=
  ∃ p : Sp k ⟶ Y.Y.X, p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ ∧ Y.Carries p (frameOf Z P)

def CarriedC {ι : c.F →+* ℂ} (P : FrPt Xo c (CAt ι)) : Prop := letI := ι.toAlgebra; Carried (k := ℂ) Y P

def CoordAtC {ι : c.F →+* ℂ} (P : FrPt Xo c (CAt ι)) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : ℂ) : Prop :=
  letI := ι.toAlgebra; CoordAt (k := ℂ) Y P n σ a

variable {Y}

theorem CoordAt.const_mul {k : Type} [Field k] [Algebra c.F k] {P : FrPt Xo c k} {n : Letter Dw → ℤ} {σ : Y.Y.Fn} {a : k}
    (h : CoordAt Y P n σ a) (b : c.F) : CoordAt Y P n (constF e Y.Y b * σ) (algebraMap c.F k b * a) :=
  h.imp fun _ hp => ⟨hp.1, hp.2.const_mul Y b⟩

theorem coordAt_const_mul_iff {k : Type} [Field k] [Algebra c.F k] {P : FrPt Xo c k} {n : Letter Dw → ℤ} {σ : Y.Y.Fn}
    {a : k} {b : c.F} (hb : b ≠ 0) :
    CoordAt Y P n (constF e Y.Y b * σ) a ↔ CoordAt Y P n σ (algebraMap c.F k b⁻¹ * a) := by
  constructor
  · intro h
    have := h.const_mul b⁻¹
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hb, map_one, one_mul] at this
  · intro h
    have := h.const_mul b
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hb, map_one, one_mul] at this

theorem CoordAt.carried {k : Type} [Field k] [Algebra c.F k] {P : FrPt Xo c k} {n : Letter Dw → ℤ} {σ : Y.Y.Fn} {a : k}
    (h : CoordAt Y P n σ a) : Carried Y P := h.imp fun _ hp => ⟨hp.1, hp.2.carries Y⟩

variable {r : ℕ}

end Free

end GlobalTheory.ShFam.Pad
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad.LineTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem expo_add (w w' : Sym E →₀ ℤ) : expo Dw (w + w') = expo Dw w + expo Dw w' := by
  classical
  funext x
  simp only [expo, Pi.add_apply]
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b c; split_ifs <;> simp

theorem expo_zero : expo Dw 0 = 0 := by
  funext x; simp [expo]

open Classical in
theorem expo_single (a : Sym E) (n : ℤ) (x : Letter Dw) :
    expo Dw (Finsupp.single a n) x = if letterOf Dw a.2.2 = some x then n else 0 := by
  simp only [expo]
  rw [Finsupp.sum_single_index]
  simp

theorem imaginary_root_ne_zero : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h
  have h1 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
  have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h3 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, h1] at h2
  nlinarith [mul_self_nonneg H.rt0.re]

theorem mult_of_mem {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : Dw.mult τ = Dw.p := by
  simp [Datum.mult, h]

theorem mult_conj_of_mem {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : Dw.mult (conjEmb τ) = Dw.q := by
  have : conjEmb τ (H.rt : E) ≠ H.rt0 := by
    simpa [conjEmb, h] using imaginary_root_ne_zero (H := H)
  simp [Datum.mult, this]

theorem expo_root_first (a : ℕ → Bool) (R : Option ℝ) {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) (i : ℕ) (hi : i < Dw.p) :
    expo Dw (rootSym Dw a R τ i) ⟨τ, ⟨i, by rw [mult_of_mem Dw h]; exact hi⟩⟩ = 1 := by
  have : i < Dw.mult τ := by rw [mult_of_mem Dw h]; exact hi
  simp [rootSym, hi, expo_single, letterOf, this]

theorem expo_root_second (a : ℕ → Bool) (R : Option ℝ) {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) (i : ℕ)
    (hi : Dw.p ≤ i) (hi' : i < Dw.p + Dw.q) :
    expo Dw (rootSym Dw a R τ i)
      ⟨conjEmb τ, ⟨Dw.p + Dw.q - 1 - i, by rw [mult_conj_of_mem Dw h]; omega⟩⟩ = -1 := by
  have : Dw.p + Dw.q - 1 - i < Dw.mult (conjEmb τ) := by rw [mult_conj_of_mem Dw h]; omega
  have h' : ¬ i < Dw.p := by omega
  rw [rootSym, if_neg h', expo_single]
  simp [letterOf, this]

theorem parOf_eq {w : Sym E →₀ ℤ} {R : Option ℝ} (h0 : w ≠ 0) (h : ∀ a ∈ w.support, a.2.1 = R) : parOf w = R := by
  have hne : w.support.Nonempty := Finsupp.support_nonempty_iff.2 h0
  rw [parOf, dif_pos hne]
  exact h _ hne.choose_spec

theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  simp only [letters, List.mem_flatMap, List.mem_map]
  exact ⟨a, List.mem_finRange a, i, List.mem_finRange i, rfl⟩

theorem length_letters : (letters Dw).length = ∑ τ : E →+* ℂ, Dw.mult τ := by
  simp only [letters, List.length_flatMap, List.length_map, List.length_finRange]
  rw [← Fin.sum_univ_def]
  exact (Fintype.equivFin (E →+* ℂ)).symm.sum_comp (fun τ => Dw.mult τ)

variable {Dw} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem divOf_add (n n' : Letter Dw → ℤ) : divOf Y (n + n') = divOf Y n + divOf Y n' := by
  simp [divOf, add_smul, Finset.sum_add_distrib]

theorem divOf_eq_neg (ex : Ix Dw → ℤ) : divOf Y (fun x => ex (some x)) = -Y.LEx ex := by
  simp [divOf, FlagCpt.LEx]

theorem isEqn_divOf (n : Letter Dw → ℤ) (y : Y.Y.X) :
    (divOf Y n).IsEqn y (∏ x : Letter Dw, (Y.gr_spec y).choose_spec.choose_spec.choose x.1 x.2 ^ n x) := by
  classical
  have h := (Y.gr_spec y).choose_spec.choose_spec.choose_spec.2
  unfold divOf
  induction (Finset.univ : Finset (Letter Dw)) using Finset.induction_on with
  | empty => simpa using CartierDiv.isEqn_zero y
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha]; exact ((h a.1 a.2).zsmul _).add ih

theorem residueCharacteristic_prime (v : HeightOneSpectrum (𝓞 F)) : (resP v).Prime := by
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  exact CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _

variable {D : D7} {A : Amb D}

theorem mem_setB (κ : Lv A) (B : ℝ) (hB : 0 ≤ B) (p : ℕ) :
    p ∈ setB κ B ↔ p.Prime ∧ ((p : ℝ) ≤ B ∨ p = 2 ∨ p ∣ (discr D.host.E).natAbs ∨ p ∣ κ.l.M') := by
  have h1 : (discr D.host.E).natAbs ≠ 0 := by simpa using discr_ne_zero D.host.E
  have h2 : κ.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := κ.l.three_le; omega) κ.l.A_pos.ne'
  simp only [setB, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors, Nat.lt_succ_iff,
    Nat.le_floor_iff hB]
  constructor
  · rintro (⟨a, b⟩ | ⟨a, b, -⟩)
    · exact ⟨b, .inl a⟩
    · refine ⟨a, .inr ?_⟩
      rcases (Nat.Prime.dvd_mul a).1 b with b | b
      · rcases (Nat.Prime.dvd_mul a).1 b with b | b
        · exact .inl ((Nat.prime_dvd_prime_iff_eq a Nat.prime_two).1 b)
        · exact .inr (.inl b)
      · exact .inr (.inr b)
  · rintro ⟨a, b | b | b | b⟩
    · exact .inl ⟨b, a⟩
    · exact .inr ⟨a, b ▸ (dvd_mul_right _ _).mul_right _, by positivity⟩
    · exact .inr ⟨a, (b.mul_left _).mul_right _, by positivity⟩
    · exact .inr ⟨a, b.mul_left _, by positivity⟩

end GlobalTheory.ShFam.Pad.LineTest
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM

namespace GlobalTheory.ShFam.Pad

structure FinLB (X : Scheme.{0}) : Type where
  n : ℕ
  U : Fin n → X.Opens
  g : ∀ i k, Γ(X, U i ⊓ U k)ˣ
  isLB : LB.IsLB ⟨Fin n, U, g⟩

abbrev FinLB.lb {X : Scheme.{0}} (L : FinLB X) : LB X := ⟨Fin L.n, L.U, L.g⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure LineModel (Z : Mdl Y i₀) (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw) : Type where
  L : FinLB Z.X
  r : ∀ (a : Fin Z.m) (i : Fin L.n), Γ(Z.X, (Z.U a).1 ⊓ L.U i)ˣ
  trans : ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a i i', ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (L.U i ⊓ L.U i')) →
    valF w _ (r a i').val = valF w _ (L.g i i').val * valF w _ (r a i).val
  chart : ∀ (k : Type) [Field k] a a' i (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k)
    (cf : Fin (Dw.mult x.1) → k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' →
    ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ L.U i → (∀ m, x.2 < m → cf m = 0) →
    IsCombAtG (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ x.1) cf ((Z.fr a').bc φ' x.1 x.2) →
    valF (spMap φ ≫ Z.chart a) _ (r a i).val = valF (spMap φ ≫ Z.chart a) _ (r a' i).val * cf x.2
  norm : ∀ (y : Z.Pt) a i (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen → ⊤ ≤ y.z ⁻¹ᵁ L.U i →
    Real.log ‖valF y.gen _ (r a i).val‖ + lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p b st = 0

structure admitted (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where
  Z : Mdl Y i₀
  full : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ
  n : ℕ
  lvl : Z.i.l.M = i₀.l.M ∧ Z.i.l.Mb = i₀.l.Mb ∧ Z.i.l.A = i₀.l.A * p ^ n
  line : ∀ (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw), letterOf Dw st = some x → LineModel Z b st x

variable {D : D7}

open Classical in

def placeW (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ) : ValuationSubring ℂ :=
  Classical.epsilon fun W => (∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ la.1.valuation D.what₂.LL x ≤ 1) ∧
    ∀ a : DV.KW p, jc a ∈ W ↔ a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range

abbrev AdmAt {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) {p : ℕ} (hp : p.Prime) {W : ValuationSubring ℂ}
    (hW : (p : ℂ) ∈ W.nonunits) : Type :=
  admitted (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩

def AdmEx {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (n : ℕ),
    1 + 1 / ((p : ℝ) - 1) < n → ∃ z : AdmAt S κ hp hW, z.n = n

end GlobalTheory.ShFam.Pad
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotRedDouble
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlagCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {F : Type} [Field F] {Z : Model Xo c β} {e : F ≃+* c.F}

theorem join_over [Mono (genι Z)] (C : FlagCpt Z e) (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (w : Sp (DualNumber C.Y.Fn) ⟶ Z.oF.t.G.left) (hw : w ≫ Z.m.φ = C.f0.v τ i) :
    w ≫ Z.oF.t.G.hom = spMap (algebraMap C.Y.Fn (DualNumber C.Y.Fn)) ≫
      (letI := (constF e C.Y).toAlgebra; GlobalTheory.AllWt.ptF C.y0) := by
  have := Z.jQ_open
  rw [← cancel_mono Z.jQ, ← cancel_mono (genι Z)]
  have h1 := (C.f0.tan τ i).1
  rw [← hw, Category.assoc, Z.m.cart.1.w] at h1
  have h2 := congrArg (· ≫ genι Z) C.y0_x
  simp only [Category.assoc] at h1 h2 ⊢
  rw [h2]
  exact h1

theorem mono_genι (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : Mono (genι Y) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)) :=
    IsLocalization.epi (nonZeroDivisors (𝓞 c.F)) c.F
  have : Mono (spMap (algebraMap (𝓞 c.F) c.F)) :=
    Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)).op
  infer_instance

theorem Lw_weightOf (C : FlagCpt Z e) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    C.Lw (GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ)) = C.LEx (exKey Dw a n) := by
  have h : GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ) =
      GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ) + ((n / 2 : ℕ) : ℤ)) 0 := by
    funext τ j
    simp only [GlobalTheory.AllWt.weightOf]
    split_ifs <;> ring
  rw [FlagCpt.Lw, h, GlobalTheory.AllWt.exOf_weightOf]
  simp only [FlagCpt.LEx, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp [exKey, keyEx, ex, exZ]

theorem exKey_none (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Even n) : exKey Dw a n none = 0 := by
  obtain ⟨m, rfl⟩ := hn
  simp only [exKey, keyEx, ex]
  omega

theorem dim_count (f p q : ℕ) :
    f * ((p + q) * (p + q - 1) / 2) = f * p * q + f * (p * (p - 1) / 2) + f * (q * (q - 1) / 2) := by
  have h : (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ' (p + q), Nat.choose_succ_succ' q, ih]
      simp only [Nat.choose_one_right]; ring
  simp only [← Nat.choose_two_right, h]; ring

theorem genericPt_eq (Y : GlobalTheory.ProjVar.Var F) (y : Y.X) :
    genericPt Y = spMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) ≫ stalkPt Y y :=
  (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y.X).specializes trivial)).symm

theorem cover {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}
    (Φ : FlagTor Z e U) (z : gen Z) : ∃ i, z ∈ Set.range (Φ.C i).π := by
  let k := AlgebraicClosure ((gen Z).residueField z)
  let x : Sp k ⟶ gen Z := spMap (algebraMap ((gen Z).residueField z) k) ≫ (gen Z).fromSpecResidueField z
  let φ : c.F →+* k := (Spec.preimage (x ≫ genStr Z)).hom
  have hφ : x ≫ genStr Z = spMap φ := (Spec.map_preimage _).symm
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z k φ x hφ
  obtain ⟨p, ⟨hp, -⟩, -⟩ := Φ.lifts k φ x hφ g
  let s : Sp k := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  refine ⟨p.1, p.2 s, ?_⟩
  rw [← Scheme.Hom.comp_apply, hp]
  exact Scheme.fromSpecResidueField_apply z _

theorem comp_eq {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) {k : Type} [Field k]
    [IsAlgClosed k] {φ : c.F →+* k} {x : Sp k ⟶ gen Z} (hx : x ≫ genStr Z = spMap φ) (g : EigFrame Z φ (x ≫ genι Z))
    {i j : U.Comp} {p : Sp k ⟶ (Φ.C i).Y.X} {q : Sp k ⟶ (Φ.C j).Y.X} (hp : p ≫ (Φ.C i).π = x) (hq : q ≫ (Φ.C j).π = x)
    (cp : (Φ.C i).Carries p g) (cq : (Φ.C j).Carries q g) : i = j :=
  congrArg Sigma.fst ((Φ.lifts k φ x hx g).unique (y₁ := ⟨i, p⟩) (y₂ := ⟨j, q⟩) ⟨hp, cp⟩ ⟨hq, cq⟩)

theorem bd_eq_zero (C : FlagCpt Z e) (h : ∀ y, C.π y ∉ genBd Z) : C.bd = 0 := by
  refine CartierDiv.ext_of_isEqn fun y => ?_
  have h1 : y ∉ C.bd.supp := fun hy => h y ((C.bd_supp y).1 hy)
  obtain ⟨g', hg', hu⟩ := CartierDiv.notMem_supp_iff.1 h1
  refine ⟨1, hg'.iff_unitAt.2 ?_, CartierDiv.isEqn_zero y⟩
  simpa using hu.inv

theorem not_red_double (Y : GlobalTheory.ProjVar.Var F) (Δ : Y.Dv) (hΔ : Y.Eff Δ) (y : Y.X) (hy : y ∈ Y.supp Δ) :
    ¬ ∀ (y : Y.X) (g : Y.Fnˣ), (2 • Δ).IsEqn y g → ∀ (f : Y.Fn) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) →
      RegAt y (f / g) := fun h => by
  obtain ⟨g, hg⟩ := Δ.exists_isEqn y
  have hr : RegAt y (g : Y.Fn) := by simpa using hg.regularAt_iff.1 (hΔ y)
  have h2 := h y (g ^ 2) (hg.nsmul 2) g 2 hr (by simpa using (unitAt_one y).regAt)
  have h3 : RegAt y (g : Y.Fn)⁻¹ := by
    convert h2 using 1
    rw [Units.val_pow_eq_pow_val]; field_simp
  refine CartierDiv.notMem_supp_iff.2 ⟨g, hg, ?_⟩ hy
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := h3
  refine ⟨a, IsUnit.of_mul_eq_one b (IsFractionRing.injective _ Y.X.functionField ?_), by rw [one_mul]; exact ha⟩
  rw [map_mul, map_one]
  exact (congrArg₂ (· * ·) ha hb).trans (mul_inv_cancel₀ g.ne_zero)

end GlobalTheory.ShFam.FlagCheck
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PeriodComparisonProvisional
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam

variable {D : D7}

section Same

theorem samePt_of_heq {r j p r' j' : ℕ} {Λ : ModuliIntegralCharts.Loc D r j p} {Λ' : ModuliIntegralCharts.Loc D r' j' p} (hr : r = r') (hj : j = j')
    (hΛ : HEq Λ Λ') {y : Λ.Pt Λ.YY} {y' : Λ'.Pt Λ'.YY} (hy : HEq y y') :
    Λ.fld y = Λ'.fld y' ∧
      (∃ e : Λ.Ylat y ≃ₗ[𝓞 D.host.E] Λ'.Ylat y', ∀ a b, Λ'.be y' (e a) (e b) = Λ.be y a b) ∧
      (Λ.good y ↔ Λ'.good y') ∧ Λ.phiCy y = Λ'.phiCy y' ∧ Λ.dP y = Λ'.dP y' := by
  subst hr hj; cases hΛ; cases hy
  exact ⟨rfl, ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩, Iff.rfl, rfl, rfl⟩

theorem lat_of_heq {r j p r' j' : ℕ} {Λ : ModuliIntegralCharts.Loc D r j p} {Λ' : ModuliIntegralCharts.Loc D r' j' p} (hr : r = r') (hj : j = j')
    (hΛ : HEq Λ Λ') {y : Λ.Pt Λ.YY} {y' : Λ'.Pt Λ'.YY} (hy : HEq y y') {Y : Type} [AddCommGroup Y]
    [Module (𝓞 D.host.E) Y] (β : Y → Y → ℝ)
    (hY : ∃ e : Λ.Ylat y ≃ₗ[𝓞 D.host.E] Y, ∀ a b, β (e a) (e b) = Λ.be y a b) :
    ∃ e : Λ'.Ylat y' ≃ₗ[𝓞 D.host.E] Y, ∀ a b, β (e a) (e b) = Λ'.be y' a b := by
  subst hr hj; cases hΛ; cases hy; exact hY

theorem pt_eq_of_heq {r j p r' j' : ℕ} {Λ : ModuliIntegralCharts.Loc D r j p} {Λ' : ModuliIntegralCharts.Loc D r' j' p} (hr : r = r') (hj : j = j')
    (hΛ : HEq Λ Λ') : Λ.Pt Λ.YY = Λ'.Pt Λ'.YY := by
  subst hr hj; cases hΛ; rfl

theorem loc_heq_of_eq {P P' : ModuliIntegralCharts.Prov D} (hP : P = P') {d : P.Dat} {d' : P'.Dat} (hd : HEq d d') (p : ℕ) :
    HEq (P.loc d p) (P'.loc d' p) := by
  subst hP; cases hd; rfl

end Same

section Comparison₂

variable {T : Top D} (h : LawsP T) {F : SrcFam (ambOf T.Q h.pins.1)} (t : ParTie T.Q h.pins.1 F) {L : CmList (ambOf T.Q h.pins.1)}
  {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C) {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (k : Kits F L C jC ng)

def LocTie : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ p,
  HEq (T.G.P.loc (T.G.dat j) p) ((k.at (datW D F.κg j)).pad.loc p)

variable {h t K R k}

theorem rk_dat_eq (h : LawsP T) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) :
    T.G.P.rk (T.G.dat j) = (datW D κ j).N :=
  (h.datum_condition j h1 hm).1.trans (datW_N D κ j).symm

theorem jj_dat_eq (h : LawsP T) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) :
    T.G.P.jj (T.G.dat j) = (datW D κ j).j :=
  (h.datum_condition j h1 hm).2.trans (datW_j D κ h1 hm.le).symm

theorem LocTie.pts (H : LocTie h k) : PtsTie h k := fun j h1 hm p =>
  pt_eq_of_heq (rk_dat_eq h F.κg h1 hm) (jj_dat_eq h F.κg h1 hm) (H j h1 hm p)

theorem LocTie.samePt (H : LocTie h k) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {p : ℕ} {η : T.G.PY j p}
    {η' : ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY} (he : HEq η η') :
    (T.G.P.loc (T.G.dat j) p).fld η = ((k.at (datW D F.κg j)).pad.loc p).fld η' ∧
      (∃ e : (T.G.P.loc (T.G.dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] ((k.at (datW D F.κg j)).pad.loc p).Ylat η',
        ∀ a b, ((k.at (datW D F.κg j)).pad.loc p).be η' (e a) (e b) = (T.G.P.loc (T.G.dat j) p).be η a b) ∧
      ((T.G.P.loc (T.G.dat j) p).good η ↔ ((k.at (datW D F.κg j)).pad.loc p).good η') ∧
      (T.G.P.loc (T.G.dat j) p).phiCy η = ((k.at (datW D F.κg j)).pad.loc p).phiCy η' ∧
      (T.G.P.loc (T.G.dat j) p).dP η = ((k.at (datW D F.κg j)).pad.loc p).dP η' :=
  samePt_of_heq (rk_dat_eq h F.κg h1 hm) (jj_dat_eq h F.κg h1 hm) (H j h1 hm p) he

theorem LocTie.lat (H : LocTie h k) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {la : HeightOneSpectrum (𝓞 T.Q.c.F)}
    {z : PointsOfFlagModel.Pt (T.G.Tw j (WeightAlgebra.resCh la)) .yy} (hz : T.G.IsAlgPt j la z) {η : T.G.PY j (WeightAlgebra.resCh la)}
    (hr : T.G.rel j _ η z)
    {η' : ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).Pt ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).YY}
    (he : HEq η η') (A : DatAt ((T.G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1) :
    ∃ e : ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).Ylat η' ≃ₗ[𝓞 D.host.E] A.Ylat,
      ∀ a b, A.beta (e a) (e b) = ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).be η' a b :=
  lat_of_heq (rk_dat_eq h F.κg h1 hm) (jj_dat_eq h F.κg h1 hm) (H j h1 hm _) he (fun a b => A.beta a b)
    (h.lattice_condition j h1 hm la z hz η hr A)

theorem LocTie.localTie_of_provisional (K : CutSt C) (R : ResSt C) {I : Type} {dat : I → Dat D (Lv (ambOf T.Q h.pins.1))}
    {hI : ∀ i, (dat i).Indef} {iW : ℕ → I} (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j)
    (hP : T.G.P = indefiniteDataFamily (shimOf K R k) I dat hI) (hd : ∀ j, 1 ≤ j → j < D.R.m → HEq (T.G.dat j) (iW j)) :
    LocTie h k := fun j h1 hm p => by
  refine (loc_heq_of_eq hP (hd j h1 hm) p).trans ?_
  show HEq ((k.at (dat (iW j))).pad.loc p) _
  rw [hiW j h1 hm]

example {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {p : ℕ} {η : T.G.PY j p}
    {η' : ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY} (he : HEq η η')
    (hη : (T.G.P.loc (T.G.dat j) p).good η) (hη' : ¬ ((k.at (datW D F.κg j)).pad.loc p).good η') : ¬ LocTie h k :=
  fun H => hη' ((H.samePt h1 hm he).2.2.1.1 hη)

example {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {p : ℕ} {η : T.G.PY j p}
    {η' : ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY} (he : HEq η η')
    (hne : (T.G.P.loc (T.G.dat j) p).phiCy η ≠ ((k.at (datW D F.κg j)).pad.loc p).phiCy η') : ¬ LocTie h k :=
  fun H => hne (H.samePt h1 hm he).2.2.2.1

section Phi

variable {P : FormsOver K R k} (hg : F.κg.primes = Finset.univ.image D.host.g)
  {I : Type} {dat : I → Dat D (Lv (ambOf T.Q h.pins.1))} (hI : ∀ i, (dat i).Indef) {iW : ℕ → I}
  (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D (famOf K R k hg P).κg j)

end Phi

end Comparison₂

end GlobalTheory.ShFam
end
end

