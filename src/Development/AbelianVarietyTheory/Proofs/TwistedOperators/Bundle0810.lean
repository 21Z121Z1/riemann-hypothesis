import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0809
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0655
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0776
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0402
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0421
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0605
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0717
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0412
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTrianglePeriodAlgebraicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_period_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  first | exact @GlobalTheory.BotAlgI.classSums_algebraic | exact GlobalTheory.BotAlgI.classSums_algebraic | (intros; apply GlobalTheory.BotAlgI.classSums_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DownEqLiftP
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

theorem bplus_eq_per {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    (M : GlobalTheory.FunObj.Vol G) (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus Wl M φ F = (topLev G hM).per Wl.ψ φ F :=
  GlobalTheory.T.besselPeriodCorankOneLess_eq_topBesselLevel_period G Wl t M hM φ F

end GlobalTheory.RowChain

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem restrictPol_comp (P : PolE G) {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z),
    restrictPol P (p.comp q) = Path.Fam.append (restrictPol P p) (restrictPol P q)
  | _, .nil => rfl
  | _, .snoc a q => by
    show (restrictPol P (p.comp q), polOf P a) = (Path.Fam.append (restrictPol P p) (restrictPol P q), polOf P a)
    rw [restrictPol_comp P p q]

theorem zip_append {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) {X Y : Node} {p : Path T X Y} (d : p.Fam S)
    (d' : p.Fam S') : ∀ {Z : Node} (q : Path T Y Z) (e : q.Fam S) (e' : q.Fam S'),
    Path.Fam.zip φ (d.append e) (d'.append e') = (Path.Fam.zip φ d d').append (Path.Fam.zip φ e e')
  | _, .nil, _, _ => rfl
  | _, .snoc a q, e, e' => by
    show (Path.Fam.zip φ (d.append e.1) (d'.append e'.1), φ a e.2 e'.2) =
      ((Path.Fam.zip φ d d').append (Path.Fam.zip φ e.1 e'.1), φ a e.2 e'.2)
    rw [zip_append φ d d' q e.1 e'.1]

theorem zip_rowFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (j : ℕ) : ∀ n (f : ∀ i : Fin n, S (.right i j))
    (g : ∀ i : Fin n, S' (.right i j)), Path.Fam.zip φ (rowFam j n f) (rowFam j n g) = rowFam j n fun i => φ _ (f i) (g i)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show (Path.Fam.zip φ (rowFam j n fun i => f i.castSucc) (rowFam j n fun i => g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n))) =
      (rowFam j n fun i => φ _ (f i.castSucc) (g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n)))
    rw [zip_rowFam φ j n]

theorem zip_downFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (t : T) (i : ℕ) : ∀ n (f : ∀ j : Fin n, S (.down t i j))
    (g : ∀ j : Fin n, S' (.down t i j)), Path.Fam.zip φ (downFam t i n f) (downFam t i n g) = downFam t i n fun j => φ _ (f j) (g j)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show Path.Fam.zip φ (Path.Fam.append (p := Path.one (.down t i n)) ((), f (Fin.last n)) (downFam t i n fun j => f j.castSucc))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), g (Fin.last n)) (downFam t i n fun j => g j.castSucc)) =
      Path.Fam.append (p := Path.one (.down t i n)) ((), φ _ (f (Fin.last n)) (g (Fin.last n)))
        (downFam t i n fun j => φ _ (f j.castSucc) (g j.castSucc))
    refine (zip_append φ (p := Path.one (.down t i n)) (((), f (Fin.last n)) : (Path.one (.down t i n)).Fam S)
      (((), g (Fin.last n)) : (Path.one (.down t i n)).Fam S') (downPath t i n) (downFam t i n fun j => f j.castSucc)
      (downFam t i n fun j => g j.castSucc)).trans ?_
    rw [zip_downFam φ t i n]
    rfl

theorem restrictPol_rowPath (P : PolE G) (j : ℕ) : ∀ n, restrictPol P (rowPath T j n) = rowFam j n fun i => polOf P (.right i j)
  | 0 => rfl
  | n + 1 => by
    show (restrictPol P (rowPath T j n), polOf P (.right n j)) = (rowFam j n fun i => polOf P (.right (i.castSucc : Fin (n + 1)) j), _)
    rw [restrictPol_rowPath P j n]
    rfl

theorem restrictPol_downPath (P : PolE G) (t : T) (i : ℕ) : ∀ n,
    restrictPol P (downPath t i n) = downFam t i n fun j => polOf P (.down t i j)
  | 0 => rfl
  | n + 1 => by
    show restrictPol P ((Path.one (.down t i n)).comp (downPath t i n)) = _
    rw [restrictPol_comp, restrictPol_downPath P t i n]
    rfl

theorem tensE_single (W : G.Weil) {X Y : Node} (p : Path T X Y) (P : PolE G) (d : PureT G p) (c : ℂ) :
    tensE W p (Finsupp.single P 1) (Finsupp.single d c) =
      Finsupp.single (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P p)) c := by
  unfold tensE tensT
  rw [Finsupp.mapDomain_single, Finsupp.sum_single_index, Finsupp.sum_single_index, one_mul]
  · simp
  · simp

theorem zip_given (W : G.Weil) (t : T) (ρ : G.RealVec) (q : ∀ j : ℕ, PolF D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank)
    (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j)) (Φ : G.Datum) :
    Path.Fam.zip (fun a (g : Sch G a) Q => W.fock a.pair g Q) (givenFin W t f Φ) (restrictPol (gPol ρ q) (givenPath t D.R.m)) =
      Path.Fam.append (colPure W t f fun j => q j) (rowDatum W ρ Φ) := by
  unfold givenFin givenPath
  rw [restrictPol_comp, zip_append, restrictPol_downPath, restrictPol_rowPath, zip_downFam, zip_rowFam]
  congr 1
  unfold rowDatum
  congr 1
  funext i
  show W.fock (.chi i 0) (W.cosVec i (Φ i)) (if h : (i : ℕ) < D.R.m then ρ ⟨i, h⟩ else 0) = W.datum ρ Φ i
  rw [dif_pos i.2]
  rfl

end GlobalTheory.FlipStart

open GlobalTheory.FlipStart in

theorem GlobalTheory.FlipStart.start : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro hP hC
  obtain ⟨a, h⟩ := ((GlobalTheory.T.path_convergence_down_chain hP hC).and (GlobalTheory.T.path_convergence_horizontal_theta hP hC)).and (GlobalTheory.T.given_finite_representation_chain hP)
  refine ⟨a, fun ε CF hCF => ?_⟩
  obtain ⟨x, h⟩ := h ε CF hCF
  refine ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  obtain ⟨⟨hcol, hrow⟩, hfin⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  obtain ⟨q, hq⟩ := exists_chainPols ch
  refine ⟨Finsupp.single (gPol ch.ρ q) 1, fun t => ?_⟩
  obtain ⟨f, hf⟩ := exists_chainVecs ch t
  obtain ⟨z, hz, hrep⟩ := hfin t f hf
  refine ⟨z, hz, fun Φ => ⟨Finsupp.single (givenFin ch.W t f Φ) (z : ℂ), hrep Φ, fun M hM y => ?_⟩⟩
  obtain ⟨hc1, hc2⟩ := hcol t f q hf hq M hM y
  obtain ⟨hr1, hr2⟩ := hrow t Φ M hM y
  rw [tensE_single]
  refine ⟨fun d hd => ?_, ?_⟩
  · have hd' := Finsupp.support_single_subset hd
    rw [Finset.mem_singleton] at hd'
    subst hd'
    rw [zip_given]
    refine (pathConv_comp ch.W M _ _ _ _ _).2 ⟨hc1, ?_⟩
    rw [hc2]
    exact hr1
  · rw [liftT_single, zip_given]
    unfold givenPath
    rw [pathLift_comp, hc2, ← hr2, smul_smul, inv_mul_cancel₀ (Units.ne_zero z), one_smul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsDoublingFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
open scoped Classical
namespace GlobalTheory.PlacePureFin
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

theorem side {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    (om : Rep σ Y Wd) (h : UA σ Wd.J)
    (hloc : ∀ v, ∀ hh ∈ UAt σ Wd (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, hh)) φ φ₁)
    (S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F))
    (hfix : ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (e : AF F) (he : e * e = e), S₀ ⊆ S →
      (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u * e = 0) →
      (∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * e = 0 ∨ u * e = u) →
      ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F w) → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
        om (1, loc e he h) (pure f φ) = pure f φ)
    (f : SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v) ∧
      (∀ v, Acts (evFin F v) (om (1, loc (idem F v) (idem_mul_self v) h)) (φ v) (φ₁ v)) ∧
      om (1, h) (pure f φ) = pure f φ₁ := by
  have hvAt : ∀ v, loc (idem F v) (idem_mul_self v) h ∈ UAt σ Wd (evFin F v) := by
    intro v u hu
    show u • (mat (loc (idem F v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  choose φ₁ hφ₁SB hφ₁Act using fun v => hloc v _ (hvAt v) (φ v) (hSB v)
  have hN : {v | ¬ φ v = M.vac v}.Finite := hvac
  have hN2 : {v | ¬ M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite := hM.std
  set S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) := S₀ ∪ hN.toFinset ∪ hN2.toFinset with hSdef
  have hS₀ : S₀ ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hφS : ∀ w ∉ S, φ w = M.vac w := fun w hw => by
    by_contra hc; exact hw (Finset.mem_union_left _ (Finset.mem_union_right _ (hN.mem_toFinset.2 hc)))
  have hvacS : ∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := fun w hw => by
    by_contra hc; exact hw (Finset.mem_union_right _ (hN2.mem_toFinset.2 hc))
  have hidem_at : ∀ w v (u : AF F), At (evFin F w) u → w ≠ v → u * idem F v = 0 := by
    intro w v u hu hwv
    apply mul_idem_of_evFin
    rw [← idem_mul_of_at hu, map_mul, evFin_idem, if_neg (Ne.symm hwv), zero_mul]
  have key : ∀ v ∉ S, φ₁ v = φ v := by
    intro v hv
    have hA := hφ₁Act v
    rw [hφS v hv] at hA ⊢
    refine GlobalTheory.T.vacuum_fixed_of_fixes_pureTensors_vacuaOutside F E σ M om v _ S (hM.vac v).1 hvacS (fun f' φ' hSB' hout => ?_) (φ₁ v) hA
    refine hfix S (idem F v) (idem_mul_self v) hS₀ (fun w hw u hu => hidem_at w v u hu (fun e => hv (e ▸ hw)))
      (fun w _ u hu => ?_) f' φ' hSB' hout
    by_cases hwv : w = v
    · subst hwv; right; rw [mul_comm]; exact idem_mul_of_at hu
    · left; exact hidem_at w v u hu hwv
  refine ⟨φ₁, hφ₁SB, ?_, hφ₁Act, ?_⟩
  · filter_upwards [hvac, S.eventually_cofinite_notMem] with v hv hvS
    rw [key v hvS, hv]
  · have heS : idemS F S * idemS F S = idemS F S := idemS_mul_self S
    have heS' : (1 - idemS F S) * (1 - idemS F S) = 1 - idemS F S := by
      rw [sub_mul, one_mul, mul_sub, mul_one, heS, sub_self, sub_zero]
    have horth : idemS F S * (1 - idemS F S) = 0 := by rw [mul_sub, mul_one, heS, sub_self]
    have hdec : h = (S.toList.map fun v => loc (idem F v) (idem_mul_self v) h).prod * loc (1 - idemS F S) heS' h := by
      apply ua_ext
      rw [mat_mul, mat_prod_loc h _ S.nodup_toList, Finset.toList_toFinset, mat_loc, phi_mul_orth horth,
        add_sub_cancel, phi_one]
    have hnot : ∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * idemS F S = 0 := by
      intro w hw u hu
      rw [← idem_mul_of_at hu, mul_comm (idem F w), mul_assoc, idem_mul_idemS_of_notMem hw, mul_zero]
    have hk : om (1, loc (1 - idemS F S) heS' h) (pure f φ) = pure f φ := by
      refine hfix S _ heS' hS₀ (fun w hw u hu => ?_) (fun w hw u hu => Or.inr ?_) f φ hSB hφS
      · calc u * (1 - idemS F S) = (idem F w * u) * (1 - idemS F S) := by rw [idem_mul_of_at hu]
          _ = u * (idem F w - idem F w * idemS F S) := by ring
          _ = 0 := by rw [idem_mul_idemS_of_mem hw, sub_self, mul_zero]
      · rw [mul_sub, mul_one, hnot w hw u hu, sub_zero]
    have hmul : ∀ (a b : UA σ Wd.J) (x : (Fin n × Fin d → AF F) → ℂ), om (1, a * b) x = om (1, a) (om (1, b) x) := by
      intro a b x
      have : ((1 : UA σ Y.J), a * b) = (1, a) * (1, b) := by simp
      rw [this, map_mul]; rfl
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hvac.and hM.std).mono fun v hv => hv.1.trans hv.2
    conv_lhs => rw [hdec]
    rw [hmul, hk, GlobalTheory.T.weilRep_list_prod_distinctPlaces_pureTensor F E σ om (fun v => loc (idem F v) (idem_mul_self v) h) φ φ₁ hSB hφ₁SB hφ₁Act hstd S.toList
      S.nodup_toList f]
    congr 1
    funext v
    by_cases hv : v ∈ S
    · rw [if_pos (Finset.mem_toList.2 hv)]
    · rw [if_neg (mt Finset.mem_toList.1 hv), key v hv]

theorem placePure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (W W₁ X : HSp D) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (hJ : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e), ∀ g ∈ GfC X,
    ∃ hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ v, hv v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v)) ∧
      (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om (1, hv v)) (φ v) (φ₁ v)) ∧
          om (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁) ∧
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M'.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om' (1, hv v)) (φ v) (φ₁ v)) ∧
          om' (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ := by
  intro hP D W W₁ X e Bs Γ Xc om om' R Rf hM hJ g hg
  have hT := hM.triple
  let h : UA D.sp.cm.sig Γ.W.J := GlobalTheory.TripleRead.toUX X e hJ g
  have harch : ∀ u : AF D.host.F, At (evI D.host.F) u → u • (mat h - 1) = 0 := GlobalTheory.T.finiteUnitaryPoint_darboux_trivial_archimedean D X e hJ g hg
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.unramified_places_finite_set hP _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.idempotentCut_unitaryPoint_stabilizes_lattices _ _ _ Bs _ _ Γ hT.geo h
  have hfixB : ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F)) (e : AF D.host.F) (he : e * e = e), S₀ ∪ S₁ ⊆ S →
      (∀ w ∈ S, ∀ u : AF D.host.F, At (evFin D.host.F w) u → u * e = 0) →
      (∀ w ∉ S, ∀ u : AF D.host.F, At (evFin D.host.F w) u → u * e = 0 ∨ u * e = u) →
      (∀ (f : SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, _ → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ w ∉ S, φ w = Γ.M.vac w) → om (1, loc e he h) (pure f φ) = pure f φ) ∧
      (∀ (f : SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, _ → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ w ∉ S, φ w = Γ.M'.vac w) → om' (1, loc e he h) (pure f φ) = pure f φ) := by
    intro S e he hS hin hout
    obtain ⟨hl, hl'⟩ := hS₁ S e he (Finset.subset_union_right.trans hS) hout
    refine hS₀ S (Finset.subset_union_left.trans hS) (loc e he h) ?_ ?_ hl hl'
    · intro u hu; rw [mat_loc, phi_sub_one, smul_comm, harch u hu, smul_zero]
    · intro w hw u hu; rw [mat_loc, phi_sub_one, smul_smul, hin w hw u hu, zero_smul]
  refine ⟨fun v => loc (idem _ v) (idem_mul_self v) h, fun v u hu => ?_, fun f φ hSB hvac => ?_, fun f φ hSB hvac => ?_⟩
  · show u • (mat (loc (idem _ v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  · exact side Γ.M Bs.ψ hT.geo.hM om h (fun v hh hhv φ hφ => GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW _ _ _ Bs _ _ Γ Xc om om' hT v hh hhv φ hφ)
      (S₀ ∪ S₁) (fun S e he hS hin hout => (hfixB S e he hS hin hout).1) f φ hSB hvac
  · exact side Γ.M' Bs.ψ hT.geo.hM' om' h (fun v hh hhv φ hφ => GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW _ _ _ Bs _ _ Γ Xc om om' hT v hh hhv φ hφ)
      (S₀ ∪ S₁) (fun S e he hS hin hout => (hfixB S e he hS hin hout).2) f φ hSB hvac

end GlobalTheory.PlacePureFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchKapX
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree

theorem conjU_one_eq {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem polMatch_kapX : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ g ∈ GfC X, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW 1, kapX X e hO.JX g) ΦD) (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1, kapX X e hO.JX g) Φ₀D) := by
  classical
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT R Rf hM Pi rf rl p p' _ g hg ΦD _ Φ₀D _ hPM
  rw [conjU_one_eq, conjU_one_eq]
  have hinf := GlobalTheory.T.archimedeanSupported_smul_transposeGram_finite_sub_one D X e hO.JX g hg
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.unramified_places_finite_set hP _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨T₀, hXT, hOn⟩ := hPM
  obtain ⟨S, l, k, hTS, hl, hprod, hkinf, hkS, hkV, hkV'⟩ := GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer _ _ _ Bs _ _ Γ hT.geo _ hinf (T₀ ∪ S₀)
  have ext : ∀ U : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F), GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf (T₀ ∪ U) ΦD Φ₀D := by
    intro U
    induction U using Finset.induction_on with
    | empty => rw [Finset.union_empty]; exact hOn
    | insert v U hv ih =>
      rw [Finset.union_insert]
      by_cases hvX : v ∈ Xc.T
      · rw [Finset.insert_eq_of_mem (Finset.mem_union_left _ (hXT hvX))]
        exact ih
      · exact GlobalTheory.ThK.PolynomialMatching.polMatchOn_insert _ _ _ Bs _ _ Γ Xc R Rf v (hM.fin.sph v hvX).1 _ _ _ ih
  have hOnS : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S ΦD Φ₀D := by
    have := ext S
    rwa [Finset.union_eq_right.2 (Finset.union_subset_left hTS)] at this
  have hU := hS₀ S (Finset.union_subset_right hTS) k hkinf hkS hkV hkV'
  have hOnK : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S (om (1, k) ΦD) (om' (1, k) Φ₀D) := by
    obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hOnS
    refine ⟨m, m', f, φ, f', φ', hφ, hφ', ?_, ?_, hsum⟩
    · rw [hΦ, map_sum]
      exact Finset.sum_congr rfl fun i _ => hU.1 (f i) (φ i) (hφ i).2.1 (hφ i).2.2
    · rw [hΦ', map_sum]
      exact Finset.sum_congr rfl fun j _ => hU.2 (f' j) (φ' j) (hφ' j).2.1 (hφ' j).2.2
  have split : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Φ, om (1, x * y) Φ = om (1, x) (om (1, y) Φ) := by
    intro x y Φ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have split' : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Φ, om' (1, x * y) Φ = om' (1, x) (om' (1, y) Φ) := by
    intro x y Φ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ l' : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J),
      (∀ x ∈ l', x.1 ∈ S ∧ x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F x.1)) →
      GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S (om (1, (l'.map Prod.snd).prod * k) ΦD)
        (om' (1, (l'.map Prod.snd).prod * k) Φ₀D) := by
    intro l'
    induction l' with
    | nil => intro _; simpa using hOnK
    | cons x l' ih =>
      intro hx
      have h1 := hx x List.mem_cons_self
      have h2 := ih fun y hy => hx y (List.mem_cons_of_mem _ hy)
      simp only [List.map_cons, List.prod_cons, mul_assoc]
      rw [split, split']
      exact GlobalTheory.T.matched_maps_local_identity hP _ _ _ Bs _ _ Γ Xc om om' R Rf hM S x.1 h1.1 x.2 h1.2 _ _ h2
  rw [hprod]
  exact ⟨S, hXT.trans (Finset.subset_union_left.trans hTS), key l hl⟩

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRepresentationTripleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_representation_triple : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (ρ : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pr)
      (q : PolF D X.rank W.rank →ₗ[ℂ] Pr) (q' : PolF D X.rank W₁.rank →ₗ[ℂ] Pr),
      Function.Surjective q ∧ Function.Surjective q' ∧ Module.rank ℂ Pr ≤ Cardinal.aleph0 ∧
      (∀ N : Submodule ℂ Pr, (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, ρ τ Y x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
        ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
          (∀ f, IsFinF ψ θ true A B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p (fockF ψ θ true A B f P) = φ (q P)) ∧
          ∀ f, IsFinF ψ θ false A₁ B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p' (fockF ψ θ false A₁ B f P) = φ (q' P) := by
  first | exact @GlobalTheory.RealQuot.realQuot | exact GlobalTheory.RealQuot.realQuot | (intros; apply GlobalTheory.RealQuot.realQuot <;> assumption)
end

