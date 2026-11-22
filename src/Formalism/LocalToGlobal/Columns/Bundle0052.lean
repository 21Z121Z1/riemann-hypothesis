import Formalism.LocalToGlobal.Columns.Bundle0049
import Formalism.LocalToGlobal.Columns.Bundle0045

-- bundled from Formalism.LocalToGlobal.Columns.RefKEquivOfCpTop
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem chTh_thTop_ok (A : Amb X) (u : Pr.Word) (m2 : ℕ) (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst)
    (hs : A.StepHyp (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (heqT : ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colValF W sel mu u (m2 + 1 + 1)).rho) :
    ThDist.Ok ((chTh W Ch sel mu cst A u m2).th (m2 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (colValF W sel mu u (m2 + 1)).rho
      (colValF W sel mu u (m2 + 1 + 1)).rho (rhoS Ch sel mu (m2 + 1)) (rhoT Ch sel mu (m2 + 1)) :=
  stepC_ok W Ch sel mu cst A u (m2 + 1) hm _ hT _ _ hq hs heqT

end Top

section Eq

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {Am : Amb X} {u : Pr.Word}

theorem refKEquiv_of_cpTop (hX : X.Ok) (hPr : Pr.Ok) (hF : FixE (R := R) Λ m2)
    (hY : YbHyp (R := R) sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) u m2 (oneAl Λ sel mu m2 (m2 + 1) le_rfl))
    (h2 : CpTopEquivOn W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
      (oneAl Λ sel mu m2 (m2 + 1) le_rfl) hY (Λ (m2 + 1 + 1)) (LevQFam.top X.E X.K (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K)))) :
    RefKEquiv W Λ Ch sel mu cst hQ m2 Am u (m2 + 1) := by
  classical
  intro g g' p p'
  have hmem : ∀ q : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs, q.1.y0 R.k ∈ ybSet sel mu cst q.1.N :=
    fun q => yOf_mem_ybSet sel mu cst hX hPr (pc_rowSG hQ) q _
  have e : ∀ (q : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs) (q' : ChPt (R := R) sel mu u (m2 + 1 + 1)),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) (m2 + 1) (liftQ hQ q) q' =
        cpTopK W Ch sel mu cst (chTh W Ch sel mu cst Am u m2) (m2 + 1) (liftQ hQ q) (q.1.y0 R.k) q' := by
    intro q q'
    unfold refK cpTopK
    rw [if_pos (show q.1.y0 R.k ∈ ybSet sel mu cst (liftQ hQ q : ChPt (R := R) sel mu u (m2 + 1)).deco.1.N from hmem q)]
    congr 1
    funext x
    unfold XiRef
    rw [dif_neg (by omega), dif_neg (by omega), if_pos rfl]
    rfl
  rw [e, e, lastVectorLine_equivariant hF, liftQ_oneG, liftQ_oneG]
  have h := h2 (oneG Λ sel mu g) (oneG Λ sel mu g') (liftQ hQ p) (p.1.y0 R.k) (liftQ hQ p') (hmem p)
  refine h.trans ?_
  have h1' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g'
  have h2' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g⁻¹
  show (frmRho (colValF W sel mu u (m2 + 1 + 1)) (Λ (m2 + 1 + 1)) _ (oneG Λ sel mu g')) ∘ₗ _ ∘ₗ
    (frmRho (colValF W sel mu u (m2 + 1)) (Λ (m2 + 1)) _ (oneG Λ sel mu g)⁻¹) = _
  have h3 : (oneG Λ sel mu g)⁻¹ = oneG Λ sel mu g⁻¹ := by
    unfold oneG
    simp
  rw [h3, h1', h2']
  rfl

end Eq

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.StabilizerMapTopIndexAlt
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Col Formalism.L2.Col.Sc

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct

variable (sel mu) in

structure TopFr where
  fr : ∀ (_P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (_d : DecoSet X.E (R.N R.m - 1) ∅ SG'), Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)
  spec : ∀ P d x, fr P d x ∈ localization₂ P.1.asIdeal (tilR hSG u d).1.N ↔ x ∈ stdAt X.E (R.N R.m) P.1

variable (hm : R.m = m2 + 2) (F : TopFr sel mu u hSG)

def tilPtY (d : DecoSet X.E (R.N R.m - 1) ∅ SG') : PtY W cst (L₀.withTop m2 Λt Θt) u m2 R.m (topIdx L₀ m2 Λt Θt hm) :=
  ⟨(⟨(tilR hSG u d, fun P => F.fr P d), fun P x => F.spec P d x⟩, Set.univ), by
    classical
    show Set.univ ∈ (if R.m = m2 + 1 then ybSet sel mu cst (tilR hSG u d).1.N else {Set.univ})
    rw [if_neg (by omega)]
    rfl⟩

theorem tilPtY_deco (d : DecoSet X.E (R.N R.m - 1) ∅ SG') : (tilPtY W cst L₀ u m2 Λt Θt hSG hm F d).deco = tilR hSG u d := rfl

def tilY (c : (ptGSD W ΛM).Cl) : (Formalism.L2.Col.chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).Cl :=
  clsY (topIdx L₀ m2 Λt Θt hm) (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c))

def TopLevQ : Prop :=
  ∀ (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G), s • d = d →
    ∀ (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (h : (F.fr P d)⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d ∈ GLint X.E (R.N R.m) P.1),
      (⟨_, h⟩ : ↥(GLint X.E (R.N R.m) P.1)) ∈ (Θt R.m P).H

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm F}

def extYg (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    ((Formalism.L2.Col.chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).G :=
  ((extR R hSG (s.1, s.2.1)).1, ⟨(extR R hSG (s.1, s.2.1)).2, hL s.2⟩,
    ⟨fun P => ⟨(F.fr P d)⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d,
      frame_move (F.spec P _) (F.spec P _) (localization_tilR_fixed hPr hpi hs P.1)⟩,
      fun P _ => hQ d s hs P _⟩)

theorem extYg_fst (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    (extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs).1 = (extR R hSG (s.1, s.2.1)).1 := rfl

theorem extYg_smul (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs • tilPtY W cst L₀ u m2 Λt Θt hSG hm F d =
      tilPtY W cst L₀ u m2 Λt Θt hSG hm F d := by
  have hsd : Deco.act s.1.1 s.2.1 d.1 = d.1 := by
    have h0 := congrArg Subtype.val hs
    exact h0
  have key : ∀ {N : ℕ} (hN : N = R.N R.m - 1 + 1),
      Deco.act (extUH hN s.1).1 (extGH hN s.2.1) (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 =
        (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 := by
    intro N hN
    subst hN
    have hok : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok := d.2.til (conj_piT_notMem hPr u) hpi
    have e : (DecoSet.tilH (ST := Pr.vT u) (rfl : R.N R.m - 1 + 1 = R.N R.m - 1 + 1) (Pr.piT u) d).1 =
        d.1.til (ST := Pr.vT u) (Pr.piT u) := by
      show (DecoSet.til (ST := Pr.vT u) (Pr.piT u) d).1 = _
      unfold DecoSet.til
      rw [dif_pos hok]
    rw [e]
    show Deco.act (extE s.1.1) (extG s.2.1) _ = _
    rw [← Deco.til_act, hsd]
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      show (Deco.act (extUH (N_m_succ R) s.1).1 (extGH (N_m_succ R) s.2.1)
          (DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1).res hSG =
        ((DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1).res hSG
      rw [key]
    · funext P
      show (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d *
          ((F.fr P d)⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d)⁻¹ = F.fr P d
      group
  · have hmem := (extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs •
      tilPtY W cst L₀ u m2 Λt Θt hSG hm F d).2
    classical
    change _ ∈ (if R.m = m2 + 1 then ybSet sel mu cst _ else {Set.univ}) at hmem
    rw [if_neg (by omega)] at hmem
    exact hmem

variable (sec : SecY W sel mu cst (L₀.withTop m2 Λt Θt) u m2)

def stabilizerMapMaximalIndex (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      MulAction.stabilizer ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).G
        (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
          (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
            (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c)))) where
  toFun s := ⟨(((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c)))⁻¹ *
      extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
      ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c)), by
    have h1 := ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv_smul
      (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c))
    refine MulAction.mem_stabilizer_iff.2 ?_
    show (_ * _ * _) • ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
      (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm F ((ptGSD W ΛM).outSec.rep c))) = _
    rw [mul_smul, mul_smul, h1, extYg_smul, inv_smul_eq_iff, h1]⟩
  map_one' := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ 1 _ * _ = 1
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) 1 (one_smul _ _) = 1 := by
      have e1 : (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)) = 1 := map_one (extR R hSG)
      apply Prod.ext
      · show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1 = 1
        rw [e1]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).2 = 1
          rw [e1]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (F.fr P _)⁻¹ * ((extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1.1) * F.fr P _ = 1
          rw [e1]
          have e2 : ((1 : UF X.E (R.N R.m) × GLG X.E (R.N R.m) Pr.vGs).1 : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) = 1 := rfl
          rw [e2]
          group
    rw [e, mul_one, inv_mul_cancel]
  map_mul' s t := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ (s.1 * t.1) _ * _ =
      (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) * _) *
        (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) * _)
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) (s.1 * t.1) (MulAction.mem_stabilizer_iff.1 (s * t).2) =
        extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
          extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) := by
      have em : extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1) = extR R hSG (s.1.1, s.1.2.1) * extR R hSG (t.1.1, t.1.2.1) :=
        map_mul (extR R hSG) (s.1.1, s.1.2.1) (t.1.1, t.1.2.1)
      apply Prod.ext
      · show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1 = (extR R hSG (s.1.1, s.1.2.1)).1 * (extR R hSG (t.1.1, t.1.2.1)).1
        rw [em]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).2 = (extR R hSG (s.1.1, s.1.2.1)).2 * (extR R hSG (t.1.1, t.1.2.1)).2
          rw [em]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (F.fr P _)⁻¹ * (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1.1 * F.fr P _ =
            ((F.fr P _)⁻¹ * (extR R hSG (s.1.1, s.1.2.1)).1.1 * F.fr P _) *
              ((F.fr P _)⁻¹ * (extR R hSG (t.1.1, t.1.2.1)).1.1 * F.fr P _)
          rw [em]
          show _ * ((extR R hSG (s.1.1, s.1.2.1)).1.1 * (extR R hSG (t.1.1, t.1.2.1)).1.1) * _ = _
          group
    rw [e]
    group

def stabMapY (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      FamStabS (chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m) (tilY W cst L₀ u m2 Λt Θt hSG ΛM hm F c) :=
  stabilizerMapMaximalIndex (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) sec hPr hpi hL hQ c

theorem stabMapY_injective (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (c : (ptGSD W ΛM).Cl) : Function.Injective (stabMapY (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) sec hPr hpi hL hQ c) := by
  intro a b hab
  have h1 := congrArg Subtype.val hab
  have h2 : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) a.1
        (MulAction.mem_stabilizer_iff.1 a.2) =
      extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) b.1
        (MulAction.mem_stabilizer_iff.1 b.2) :=
    mul_left_cancel (mul_right_cancel h1)
  have h3 : extUH (N_m_succ R) a.1.1 = extUH (N_m_succ R) b.1.1 := congrArg (fun g => g.1) h2
  have h4 : a.1.1 = b.1.1 := rec_extUH_injective (N_m_succ R) h3
  have ha : Deco.act a.1.1.1 a.1.2.1 ((ptGSD W ΛM).outSec.rep c).1 = ((ptGSD W ΛM).outSec.rep c).1 := by
    have h0 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 a.2)
    exact h0
  have hb : Deco.act b.1.1.1 b.1.2.1 ((ptGSD W ΛM).outSec.rep c).1 = ((ptGSD W ΛM).outSec.rep c).1 := by
    have h0 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 b.2)
    exact h0
  have hbe : ∀ w : SG', a.1.2.1 w = b.1.2.1 w := by
    intro w
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    obtain ⟨y, -, hy⟩ := ((ptGSD W ΛM).outSec.rep c).2.be_surj w (Pi.single i 1)
    have ea : (a.1.2.1 w).1.mulVec (((ptGSD W ΛM).outSec.rep c).1.be w (a.1.1.1.symm (a.1.1.1 y))) =
        ((ptGSD W ΛM).outSec.rep c).1.be w (a.1.1.1 y) :=
      congrFun (congrFun (congrArg Deco.be ha) w) _
    have eb : (b.1.2.1 w).1.mulVec (((ptGSD W ΛM).outSec.rep c).1.be w (b.1.1.1.symm (b.1.1.1 y))) =
        ((ptGSD W ΛM).outSec.rep c).1.be w (b.1.1.1 y) :=
      congrFun (congrFun (congrArg Deco.be hb) w) _
    rw [LinearEquiv.symm_apply_apply] at ea eb
    rw [h4] at ea
    rw [← hy, ea, eb]
  apply Subtype.ext
  apply Prod.ext
  · exact h4
  · apply Subtype.ext
    funext w
    exact hbe w

end Top

end Formalism.L2.Col.Sc.Fr
end
end

