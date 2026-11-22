import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartIndexInjectiveOffLastStep
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.TwTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type}
  {A : TwDat I l Z u a Ch}

theorem cosetIn_eq_empty {j : ℕ} (h : j + 1 ≠ B.R.m) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u j) : cosetIn p = fun _ => ∅ := by
  have h1 : p.1.2 = ∅ := by
    have := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) h] at this
    exact this
  funext P
  ext z
  simp [cosetIn, h1]

theorem chartIndex_injective_offLastStep (hA : A.Is) {j : ℕ} (hj : j ≤ B.R.m) (h : j + 1 ≠ B.R.m) : Function.Injective (A.b0 j) := fun α β e =>
  hA.chart_ext j hj α β e (by rw [cosetIn_eq_empty h, cosetIn_eq_empty h])

theorem subsingleton_top (hA : A.Is) : Subsingleton (Ch B.R.m) :=
  ⟨fun α β => chartIndex_injective_offLastStep hA le_rfl (by omega) (by rw [Idx.eq_top (A.b0 _ α) le_rfl, Idx.eq_top (A.b0 _ β) le_rfl])⟩

theorem finite_charts (hA : A.Is) {j : ℕ} (hj : j ≤ B.R.m) : Finite (Ch j) :=
  letI := (I.chain l u a).clsFin j
  haveI : Finite (I.stp u a j).Cl := (inferInstance : Finite ((I.chain l u a).cls j))
  Finite.of_surjective _ (hA.chOf_onto j hj)

theorem kb_top_ne_one (hI : I.Ok) (hA : A.Is) [NeZero (B.R.N B.R.m - 1)] (P : I.Q a)
    (hpi : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 1) (β : Ch B.R.m) : A.kb B.R.m β ≠ 1 := fun h =>
  TopPtModel.not_topPt_one I l Z hI P hpi (h ▸ hA.top β)

theorem bad_finite (hA : A.Is) (hG : (Formalism.L2.Forms.badG (I.rec7 l Z)).Finite) {j : ℕ} (hj : j ≤ B.R.m) : (A.bad j).Finite := by
  refine (hG.union ((I.Q a).finite_toSet.image fun P => P.under (𝓞 B.host.F))).subset fun v hv => ?_
  rcases hA.bad_le j hj v hv with h | ⟨P, hP, e⟩
  exacts [Or.inl h, Or.inr ⟨P, hP, e⟩]

theorem mem_Q_of_underQ (hI : I.Ok) {a' : I.ι} {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ I.Q a')
    (h : I.UnderQ a (P.under (𝓞 B.host.F))) : P ∈ I.Q a := by
  have key : ∀ (b : I.ι), ∀ w ∈ I.Q b, I.sel (w.under (𝓞 B.fields.F)) = w := fun b w hw => by
    unfold ColIn.Q Formalism.L2.Col.QE at hw
    split_ifs at hw with hf
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hw
      congr 1
      exact HeightOneSpectrum.ext (hI.sel_ok v)
    · exact absurd hw (Finset.notMem_empty _)
  obtain ⟨P', hP', e⟩ := h
  have e2 : P' = P := by
    rw [← key a P' hP', ← key a' P hP]
    exact congrArg I.sel e
  exact e2 ▸ hP'

set_option maxHeartbeats 800000 in

theorem exists_top_base (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    ∃ (k : TC.GA B (B.R.N B.R.m)) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u B.R.m), I.TopPt l Z u a k ∧
      TC.PtOf k (extTo I.SQ p.1.1) ∧ p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m) ∧
      ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
        Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) k = 1 := by
  obtain ⟨k, ⟨p₀, h₀, hN₀⟩, h2, -, h4⟩ := TopPtModel.exists_topPt I l Z hI hP u a
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have h1 := B.R.two_le_m
    have h2 : B.R.m ≤ B.R.m * (B.R.t + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold Ranks.N
    omega⟩
  have hb := TopPtModel.topPt_base I l Z h4
  obtain ⟨p, hp⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u (Formalism.L2.Col.DecoF.base _ _ _ _ _))
  rw [← hp] at hb
  have hN : p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m) := by
    rw [← hN₀]
    ext v
    exact (PtUniq.mem_iff_hatL (F := B.host.F) p.1.1.deco.2.lat v).trans (((hb.lat _).trans (h₀.lat _).symm).trans
      (PtUniq.mem_iff_hatL (F := B.host.F) p₀.deco.2.lat v).symm)
  refine ⟨k, p, h4, ⟨hb.uni, hb.lat, hb.f, hb.be, fun P i j => ?_⟩, hN, h2⟩
  obtain ⟨a', -, ha'⟩ := Finset.mem_biUnion.1 P.2
  have hq := (TwistPrimes.twist_primes_away I hI).2 u a' P.1 ha'
  by_cases hQ : P.1 ∈ I.Q a
  · rw [extTo_fr, ptFr_of_mem _ hq.1.2.1 hQ]
    exact hb.fr ⟨P.1, hQ⟩ i j
  · have e1 := TopPtModel.adAt_of_prV P.1 (h2 _ hq.2.2 fun h => hQ (mem_Q_of_underQ hI ha' h))
    have e2 : (extTo I.SQ p.1.1).fr P = 1 := by
      rw [extTo_fr]
      unfold ptFr GlobalTheory.Mem.Col2.latFr
      rw [dif_neg hq.1.2.1, dif_neg hQ, hN]
      exact if_pos rfl
    rw [e2]
    refine (congrFun (congrFun e1 i) j).trans ?_
    show _ = algebraMap _ _ ((Pi.single j 1 : Fin _ → B.host.E) i)
    rw [Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp

section Pin
variable {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {θ : InfFam (I.rec7 l Z)}
    {x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)} {vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ} {c₀ : ℕ → ℂ}
    {kom kom' : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))}
    {dd dd' : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ}
    {w w' : ∀ j, Ch j → Ch (j + 1) → ℂ} {Ram Ram' : ∀ j, Set (ColT I l u a j)}
    {rd rd' : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ} {cK : ℕ → ℂ}

theorem w_unique (h : PinColN A ψ θ x vac c₀ kom dd w Ram rd cK) (h' : PinColT A ψ θ x vac c₀ kom' dd' w' Ram' rd' cK)
    (j : ℕ) (hj : j < B.R.m) (α : Ch j) (γ : Ch (j + 1)) : w j α γ = w' j α γ := by
  obtain ⟨-, h1, h2⟩ := h.w_ne j hj α γ
  have e := (h.cst j hj α γ).symm.trans (h'.cst j hj α γ)
  have h3 : (volLev (x j).vol (A.U j α) : ℂ) ≠ 0 := by exact_mod_cast h1
  exact mul_left_cancel₀ h3 (mul_right_cancel₀ h2 (mul_right_cancel₀ (Circle.coe_ne_zero _)
    (mul_right_cancel₀ (inv_ne_zero (Circle.coe_ne_zero _)) e)))

theorem norm_cK (h : PinColT A ψ θ x vac c₀ kom dd w Ram rd cK) (j : ℕ) (hj : j < B.R.m) (α : Ch j) (γ : Ch (j + 1)) :
    ‖cK j‖ = |volLev (x j).vol (A.U j α)| * ‖w j α γ‖ * ‖c₀ j‖ := by
  rw [h.cst j hj α γ]
  simp [Circle.norm_coe]

end Pin

end GlobalTheory.AdForm.TwTest
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTrueWith
section
noncomputable section

namespace GlobalTheory.Core.Cls

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure TruePt (K : Ctx) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)) : Type 1 where

  isOver : K.Over B.toPre
  good : ∃ C5 c6 Cb : ℝ, K.Good C5 c6 Cb

  sc : O.L.sc = K.s
  wt : WtEq O.L K.a K.b
  val : Val K.C K.cD K.ch O.L
  canon : CanonInst O.Gx
  K_eq : O.K = K.C.GK
  cX_eq : O.cX = K.C.cX

  pin : ColPin w

  S : SelB O.ex
  std : TC.StdC w.I w.l Z S.cols
  stdLv : ∀ u, TC.StdLvC w.I w.l Z u (S.cols.forms u)
  stdDt : TC.StdDt w.I w.l Z S.full.1.base.dt
  cf_eq : S.cf = TC.cf w.I w.l Z
  xi_eq : S.tp.xi = w.I.xi
  tw_eq : O.ex.tw = w.tw Z
  lev_eq : O.ex.lev = S.full.1.base.lev0
  errX_eq : O.ex.errX = Formalism.L2.Herm.toErrXS S.full.1
  piG_eq : O.ex.errX.piG = w.px.piG
  piT_eq : O.ex.errX.piT = w.px.piT
  qp : TC.QpIs w.I O.X.Qp
  isRec : IsRecG K.s (w.D Z) O.gatT O.ex.cmp S.g.herm S.g.forms
  gpl : Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces (w.D Z) S.full.1.base.toHermColsCh S.full.1.g O.gatT
  stdKer : TC.StdKer w.I w.l Z S.ker
  stdRd : GlobalTheory.Pdv.StdRd w.I w.l Z S.ker
  entC : GlobalTheory.Pdv.IsEntC S.ker
  dsig : ∀ τ, (w.D Z).dsig τ = Vol.trueDsig B.R (B.hc τ)

abbrev TP : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), TruePt K w Z O → Prop

def IsTrueWith (P : TP) (D : D7) (O : Obj D) : Prop :=
  ∃ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O' : Obj (w.D Z)) (p : TruePt K w Z O'),
    P K B f T w Z O' p ∧ (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨w.D Z, O'⟩

def IsTrue (D : D7) (O : Obj D) : Prop := IsTrueWith (fun _ _ _ _ _ _ _ _ => True) D O

theorem IsTrueWith.ind {P : TP} {R : ∀ D : D7, Obj D → Prop}
    (h : ∀ K B f T (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)) (p : TruePt K w Z O), P K B f T w Z O p → R (w.D Z) O)
    {D : D7} {O : Obj D} (hD : IsTrueWith P D O) : R D O := by
  obtain ⟨K, B, f, T, w, Z, O', p, hp, e⟩ := hD
  cases e
  exact h K B f T w Z _ p hp

theorem IsTrue.ind {R : ∀ D : D7, Obj D → Prop}
    (h : ∀ K B f T (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), TruePt K w Z O → R (w.D Z) O)
    {D : D7} {O : Obj D} (hD : IsTrue D O) : R D O :=
  IsTrueWith.ind (fun K B f T w Z O p _ => h K B f T w Z O p) hD

theorem IsTrue.selB {D : D7} {O : Obj D} (h : IsTrue D O) : Nonempty (SelB O.ex) :=
  IsTrue.ind (R := fun _ O => Nonempty (SelB O.ex)) (fun _ _ _ _ _ _ _ p => ⟨p.S⟩) h

abbrev objF {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : Obj (Fm.D x i) :=
  ⟨Fm.L x i, Fm.gatT x i, Fm.Gx x i, Fm.Gy x i, Fm.GK, Fm.X x i, Fm.cX, Fm.ex x hx i⟩

def TrueF {eps : ℝ} (Fm : FamP eps) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), IsTrue (Fm.D x i) (objF Fm x hx i)

theorem TrueF.selBF {eps : ℝ} {Fm : FamP eps} (h : TrueF Fm) : SelBF Fm := ⟨0, fun x _ hx i => (h x hx i).selB⟩

end GlobalTheory.Core.Cls

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LiftModel

variable {D : D7} {u : D.what₂.Word}

def lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) : Lat L :=
  (𝔠 : Submodule (𝓞 D.host.E) D.host.E).map
    ((LinearMap.toSpanSingleton D.host.E (Fin L.rank → D.host.E) ζ).restrictScalars (𝓞 D.host.E))

theorem tmul_mul_incA (α : AF D.host.F) (x z : D.host.E) :
    (α ⊗ₜ[D.host.F] x : AE D) * incA D z = α ⊗ₜ[D.host.F] (x * z) := by
  change (α ⊗ₜ[D.host.F] x : AE D) * (1 ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem latV_lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (v : Pl D) :
    latV L (lineLat L ζ 𝔠) (· = v) =
      (idV 𝔠 v).map (LinearMap.toSpanSingleton (AE D) (Fin L.rank → AE D) (ratV ζ)).toAddMonoidHom := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul idV
  rw [AddMonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨α, h1, h2, a, rfl, x, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]
  · rintro ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, rfl⟩
    refine ⟨α, h1, h2, 1, rfl, _, ⟨c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]

theorem lineLatAt_lineLat (L : HSp D) {ζ : Fin L.rank → D.host.E} (hζ : ζ ≠ 0) (𝔠 : FI D) (v : Pl D) :
    LineLatAt L ζ 𝔠 (lineLat L ζ 𝔠) v := by
  intro a _
  rw [latV_lineLat]
  refine ⟨?_, fun h => ⟨a, h, rfl⟩⟩
  rintro ⟨a', h, e⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hζ
  have e1 : a' * incA D (ζ i) = a * incA D (ζ i) := congrFun e i
  have hu : IsUnit (incA D (ζ i)) := (IsUnit.mk0 _ hi).map _
  rwa [← hu.mul_right_cancel e1]

theorem idV_le_idAt (𝔞 : FI D) (v : Pl D) : ∀ a ∈ idV 𝔞 v, a ∈ idAt D (· = v) := by
  intro a ha
  refine (AddSubgroup.closure_le (idAt D (· = v)).toAddSubgroup).2 ?_ ha
  rintro _ ⟨α, -, h2, x, -, rfl⟩
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [h2 _ w.2, TensorProduct.zero_tmul]

theorem one_tmul_one_ne (F A E : Type) [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E] :
    (1 : A) ⊗ₜ[F] (1 : E) ≠ 0 := one_ne_zero (α := A ⊗[F] E)

theorem idV_ne_bot {𝔞 : FI D} (h : 𝔞 ≠ 0) (v : Pl D) : idV 𝔞 v ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (FractionalIdeal.eq_zero_iff.2 hc)
  have ev : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
    exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1
  have ew : ∀ w, w ≠ v → evalV D.host.F w (singleV D.host.F v 1) = 0 := fun w hw => by
    exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw
  intro hb
  have hm : (pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] x ∈ idV 𝔞 v := by
    refine AddSubgroup.subset_closure ⟨_, fun w => ?_, ew, x, hx, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [ev]; exact one_mem _
    · rw [ew w hw]; exact zero_mem _
  rw [hb, AddSubgroup.mem_bot] at hm
  have h2 := congrArg (fun y => compAt D v (y * incA D x⁻¹)) hm
  simp only [tmul_mul_incA, mul_inv_cancel₀ hx0, zero_mul, map_zero] at h2
  change (evalV D.host.F v (singleV D.host.F v 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0 at h2
  rw [ev] at h2
  exact one_tmul_one_ne _ _ _ h2

theorem not_lineLatAt_zero (L : HSp D) {ζ : Fin L.rank → D.host.E} (hζ : ζ ≠ 0) {𝔠 : FI D} (h : 𝔠 ≠ 0) (v : Pl D) :
    ¬ LineLatAt L ζ 𝔠 (lineLat L ζ 0) v := by
  intro hl
  refine idV_ne_bot h v ((AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_)
  have h1 := idV_le_idAt _ _ a ha
  have := (lineLatAt_lineLat L hζ 0 v a h1).1 ((hl a h1).2 ha)
  rwa [idV_zero, AddSubgroup.mem_bot] at this

theorem AA_ne (hP : FactPrincipalDatum) : D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ D.host.xi0 ≠ 0 := by
  have h1 := hP D.R D.host
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [h] at h1

theorem cols_odd_even (hP : FactPrincipalDatum) {j σ : ℕ} (h : j + 2 * (σ + 1) + 2 = D.R.m) :
    (∀ i, i < σ → D.host.AA⁻¹ * bI D j (σ + 1) i = D.host.AA * bI D (j + 1 + 1) σ i) ∧
      D.host.AA⁻¹ * bI D j (σ + 1) σ = D.host.AA * cI D (j + 1 + 1) := by
  obtain ⟨hA, hB, -⟩ := AA_ne (D := D) hP
  have key : D.host.AA⁻¹ * (dI D * cI D j) = D.host.AA * cI D (j + 1 + 1) := by
    have e := cI_step D (j := j) (by omega)
    have : dI D * cI D j = D.host.AA * D.host.AAbar * (FractionalIdeal.spanSingleton _ D.host.xi0 * cI D j) := by
      rw [dI]; ring
    rw [this, e]
    field_simp
  refine ⟨fun i hi => ?_, ?_⟩
  · have : σ + 1 - i = σ - i + 1 := by omega
    rw [bI, bI, this, pow_succ, mul_assoc, mul_left_comm, key, mul_left_comm]
  · rw [bI, Nat.add_sub_cancel_left, pow_one, key]

variable {a : XPart D u} {b : YPart a}

theorem norm_link (x y : D.host.E) (j : ℕ) (T : D.host.E) (hl : x = D.host.xi0 * star D.host.xi0 * y)
    (hx : x * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -T) :
    y * (D.host.xi0 * star D.host.xi0) ^ ((j + 1 + 1) / 2) = -T := by
  have : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
  rw [this, ← hx, hl]; ring

theorem tau_norm {ζ₀ : Fin a.Lz.rank → D.host.E} {τ} (h : b.Sk ζ₀ τ) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) :
    star (τ j hj *ᵥ ζ₀) ⬝ᵥ (b.bes j 0 hj).L.gram *ᵥ (τ j hj *ᵥ ζ₀) =
      -(D.host.xi0 * star D.host.xi0) * (((D.mem u).A.T : ℕ) : D.host.E) := by
  have e : D.R.m / 2 = j / 2 + 1 := by omega
  have n := h.norm j 0 hj
  rw [h.tau j hj, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, star_pow, e]
  linear_combination (D.host.xi0 * star D.host.xi0) * n

theorem exists_sc {k : Type} [Field k] [ValuativeRel k] {ξ c : k} (hξ : valuation k ξ = 1) (hc : valuation k c = 1) (s : ℕ) :
    ∃ sc : ℕ → k, (∀ j, valuation k (sc j) = 1) ∧ (∀ j, sc (j + 1 + 1) = sc j * ξ) ∧ -(ξ * sc s) = c * ξ ^ ((s + 1 + 1) / 2) := by
  refine ⟨fun j => -(c * ξ ^ (j / 2)), fun j => by simp [hξ, hc], fun j => ?_, ?_⟩
  · have : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
    simp only [this]; ring
  · have : (s + 1 + 1) / 2 = s / 2 + 1 := by omega
    simp only [this]; ring

theorem lineId_of_split {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (𝔠 : FI D) (v : Pl D) (h : LineLatAt L ζ 𝔠 LL v) (ho : OrthAt o M LA LL v) : LineId o ζ M 𝔠 v := by
  intro a ha
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, ← h a ha]
  rw [o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.SeeSaw.LiftModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

structure TwDat.Live {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) : Prop where
  inj : ∀ j, Function.Injective (ι j)
  first : Function.Surjective (ι 0)
  last : Function.Surjective (ι B.R.m)
  dead : ∀ j (hj : j + 1 ≤ B.R.m) γ, γ ∉ Set.range (ι (j + 1)) → ∀ α z, A.xi j hj α γ z = 0

def TwDat.RamL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) (j : ℕ) (φ : ColT I l u a j) : Prop :=
  RamT j φ ∧ ∀ c, A.chOf j c ∉ Set.range (ι j) → φ c = 0

structure PinColL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j)
    (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))
    (x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ)
    (kom : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)))
    (dd : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ)
    (w : ∀ j, Ch j → Ch (j + 1) → ℂ) (Ram : ∀ j, Set (ColT I l u a j))
    (rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ) (cK : ℕ → ℂ) : Prop where
  is : A.Is
  live : A.Live ι
  om : ∀ j, j < B.R.m → IsWeilDatumO ψ _ _ (A.chr (j + 1)) (A.chr (j + 1)) (kom j)
  dat : ∀ j (hj : j + 1 ≤ B.R.m) α γ, GlobalTheory.SeeSaw.IsFinComb (dd j α γ) ∧
    IsRatDatum ψ _ _ A.e (fun z => w j α γ * A.xi j hj (ι j α) (ι (j + 1) γ) z) (vac j) (comb ψ _ _ (dd j α γ) (vac j))
  cst : ∀ j (hj : j + 1 ≤ B.R.m) α γ, (∃ z, A.xi j hj (ι j α) (ι (j + 1) γ) z ≠ 0) →
    cK j = (volLev (x j).vol (A.U j (ι j α)) : ℂ) * w j α γ * c₀ j *
      (A.chr (j + 1) (A.xr j (ι j α)) : ℂ) * (A.chr (j + 1) (A.xr (j + 1) (ι (j + 1) γ)) : ℂ)⁻¹
  ram : ∀ j, j ≤ B.R.m → ∀ φ, φ ∈ Ram j ↔ A.RamL ι j φ
  rdq : ∀ j (hj : j ≤ B.R.m) β φ y, rd j β φ y = A.rd θ j hj (ι j β) φ y

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

@[reducible] def clsKL (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) {Ch₀ : ℕ → Type}
    (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) : ClsK (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := fun j β => {c // A.chOf j c = ι j β}
  fin := fun j _ => letI := (I.chain l u a).clsFin j; Subtype.fintype _
  U := fun j β => A.U j (ι j β)
  chi := fun j β => A.chi j (ι j β)
  h := fun j β => A.h j (ι j β)
  val := fun _ _ ψ c z => ψ c.1 ⟨z.1, z.2⟩
  abelian₂ := fun j _ _ c c' => A.abelian₂ j c.1 c'.1

def PinChL (c₀ : ℕ → ℂ) {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j)
    (w : ∀ j, k.Ch j → k.Ch (j + 1) → ℂ) : Prop :=
  PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK

structure PinTopL (UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) (ε : ℂ) : Prop where
  emb : IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  lev : ∀ h, h ∈ UT ↔ g.bT⁻¹ * h * g.bT ∈ levS _ R.βX (datXP R P t)
  eT : ∀ n h β, k.eT n h β = Finsupp.single g.bT ε
  cP : k.cP = ε * (volLev g.volT UT : ℂ)

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def Placed : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg),
    f.c.Is ∧ v.Is ∧ VTie f v ∧ ShapeOff v o ∧ GPin G ∧ GRead f G pl ∧ BotTie f B v o G

def tOf (a₀ a : GA D (D.sp.X 0)) : GA D (D.sp.Y 0) :=
  ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0)

def IsAt (a₀ a : GA D (D.sp.X 0)) : Prop :=
  IsTransportAdelicCorrection (W.S.tr u) a₀ ∧ a ∈ GfC (D.sp.X 0) ∧ a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧
    Matches W.S.X W.Q.instEq (rJ W) (rChi W) (tOf f B a₀ a)

end GlobalTheory.MiTop

end
end

