import Formalism.LocalToGlobal.Columns.Bundle0038
import Formalism.LocalToGlobal.Columns.Bundle0040
import Formalism.LocalToGlobal.Columns.Bundle0011
import Formalism.LocalToGlobal.Columns.Bundle0041

-- bundled from Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Eq

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (Am : Amb X) (u : Pr.Word)

def oneAl (j : ℕ) (h : j ≤ m2 + 1) : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β j := ⟨(), h⟩

def oneG {j : ℕ} (g : FormG (Λ j)) : FrmG (Λ j) (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))) := (g.1, g.2, 1)

variable {Λ sel mu}

theorem liftQ_oneG {j : ℕ} (g : FormG (Λ j)) (p : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) :
    (liftQ hQ ((formAct (Λ j)).toSMul.smul g p) : ChPt (R := R) sel mu u j) =
      (frmAct (Λ j) (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))).toSMul.smul (oneG Λ sel mu g) (liftQ hQ p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext ⟨P, hP⟩
    rw [hQ] at hP
    simp at hP

theorem frmRho_oneG {j : ℕ} (g : FormG (Λ j)) :
    frmRho (colValF W sel mu u j) (Λ j) (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))) (oneG Λ sel mu g) =
      formRho (colVal W u j (Pr.vT u) Pr.vGs) (Λ j) g := by
  show (((Λ j).chr g.2 * (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))).chr 1 : X.Kˣ) : X.K) •
      (colVal W u j (Pr.vT u) Pr.vGs).rho g.1 =
    (((Λ j).chr g.2 : X.Kˣ) : X.K) • (colVal W u j (Pr.vT u) Pr.vGs).rho g.1
  rw [map_one, mul_one]

variable (Λ sel mu)

def FixE : Prop :=
  ∀ h ∈ (Λ (m2 + 1)).grp, ∀ w : Pr.vGs,
    ((h w : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) : Matrix _ _ (𝓞 X.E ⧸ w.1.asIdeal)).mulVec (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k) =
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k

def RefKEquiv (i : ℕ) : Prop :=
  ∀ (g : FormG (Λ i)) (g' : FormG (Λ (i + 1))) (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) (p' : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs),
    refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i
        (liftQ hQ ((formAct (Λ i)).toSMul.smul g p)) (liftQ hQ ((formAct (Λ (i + 1))).toSMul.smul g' p')) =
      (formRho (colVal W u (i + 1) (Pr.vT u) Pr.vGs) (Λ (i + 1)) g') ∘ₗ
        (refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i (liftQ hQ p) (liftQ hQ p')) ∘ₗ
          (formRho (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) g⁻¹)

variable {W Λ Ch sel mu cst hQ m2 Am u}

theorem xiEquiv_of_refK (h : ∀ i, RefKEquiv W Λ Ch sel mu cst hQ m2 Am u i) :
    XiEquiv W Λ Ch sel mu cst Am u
      (refXi1 Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) hQ m2 (oneAl Λ sel mu m2) u) := by
  unfold XiEquiv refXi1
  intro a
  unfold ClsEq xiKer XiRef
  intro g g' p p'
  exact h a g g' p p'

theorem refKEquiv_of_mat {i : ℕ} (hi : i < m2)
    (hM : MatEquiv W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)) :
    RefKEquiv W Λ Ch sel mu cst hQ m2 Am u i := by
  intro g g' p p'
  have e : ∀ (q : ChPt (R := R) sel mu u i) (q' : ChPt (R := R) sel mu u (i + 1)),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i q q' =
        matK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) i
          (oneAl Λ sel mu m2 i (by omega)) (oneAl Λ sel mu m2 (i + 1) (by omega)) q q' := by
    intro q q'
    unfold refK matK
    congr 1
    funext x
    unfold XiRef
    rw [dif_pos hi]
  rw [e, e, liftQ_oneG, liftQ_oneG]
  have h := hM i hi (oneAl Λ sel mu m2 i (by omega)) (oneAl Λ sel mu m2 (i + 1) (by omega)) (oneG Λ sel mu g) (oneG Λ sel mu g')
    (liftQ hQ p) (liftQ hQ p')
  refine h.trans ?_
  have h1 := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g'
  have h2 := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g⁻¹
  show (frmRho (colValF W sel mu u (i + 1)) (Λ (i + 1)) _ (oneG Λ sel mu g')) ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u i) (Λ i) _ (oneG Λ sel mu g)⁻¹) = _
  have h3 : (oneG Λ sel mu g)⁻¹ = oneG Λ sel mu g⁻¹ := by
    unfold oneG
    simp
  rw [h3, h1, h2]
  rfl

theorem lastVectorLine_equivariant (hF : FixE (R := R) Λ m2) (g' : FormG (Λ (m2 + 1))) (p' : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs) :
    ((formAct (Λ (m2 + 1))).toSMul.smul g' p').1.y0 R.k = (fun v => g'.1.1 v) '' (p'.1.y0 R.k) := by
  unfold FixE at hF
  have hact : ((formAct (Λ (m2 + 1))).toSMul.smul g' p').1 = Deco.act ↑g'.1 ↑g'.2 p'.1 := rfl
  have hloc : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (y : _),
      y ∈ (Deco.act ↑g'.1 ↑g'.2 p'.1).at P ↔ g'.1.1.symm y ∈ p'.1.at P := by
    intro P y
    change (∃ s ∈ P.asIdeal.primeCompl, s • y ∈ gmap g'.1.1 p'.1.N) ↔
      (∃ s ∈ P.asIdeal.primeCompl, s • g'.1.1.symm y ∈ p'.1.N)
    constructor
    · rintro ⟨s, hs, hy⟩
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      refine ⟨s, hs, ?_⟩
      have e1 : g'.1.1.symm (s • y) = s • g'.1.1.symm y :=
        (g'.1.1.symm.toLinearMap.restrictScalars (𝓞 X.E)).map_smul s y
      rw [← e1, ← hzy]
      simpa using hz
    · rintro ⟨s, hs, hy⟩
      refine ⟨s, hs, Submodule.mem_map.mpr ⟨_, hy, ?_⟩⟩
      have e1 : g'.1.1 (s • g'.1.1.symm y) = s • g'.1.1 (g'.1.1.symm y) :=
        (g'.1.1.toLinearMap.restrictScalars (𝓞 X.E)).map_smul s _
      simpa using e1
  have hbe : ∀ (w : Pr.vGs) (y : _),
      (Deco.act ↑g'.1 ↑g'.2 p'.1).be w y = Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k ↔
        p'.1.be w (g'.1.1.symm y) = Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k := by
    intro w y
    have hM := hF g'.2.1 g'.2.2 w
    change (g'.2.1 w).1.mulVec (p'.1.be w (g'.1.1.symm y)) = _ ↔ _
    generalize p'.1.be w (g'.1.1.symm y) = z
    constructor
    · intro hz
      calc z = ((g'.2.1 w)⁻¹).1.mulVec ((g'.2.1 w).1.mulVec z) := by
            rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        _ = ((g'.2.1 w)⁻¹).1.mulVec ((g'.2.1 w).1.mulVec
              (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k)) := by
            rw [hz, hM]
        _ = _ := by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · rintro rfl
      exact hM
  rw [hact]
  ext v
  simp only [Deco.y0, Deco.yOf, Set.mem_image, Set.mem_setOf_eq, Nat.cast_smul_eq_nsmul]
  constructor
  · intro H
    refine ⟨g'.1.1.symm v, fun w => ?_, by simp⟩
    obtain ⟨h1, h2⟩ := H w
    rw [hloc, map_nsmul] at h1
    rw [hbe, map_nsmul] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨x, hx, rfl⟩ w
    obtain ⟨h1, h2⟩ := hx w
    rw [hloc, hbe, map_nsmul, LinearEquiv.symm_apply_apply]
    exact ⟨h1, h2⟩

theorem referenceKernelEquiv_of_lastComponent (hX : X.Ok) (hPr : Pr.Ok) (hF : FixE (R := R) Λ m2)
    (hY : YbHyp (R := R) sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) u m2 (oneAl Λ sel mu m2 (m2 + 1) le_rfl))
    (h1 : Cp1EquivOn W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
      (oneAl Λ sel mu m2 (m2 + 1) le_rfl) hY) :
    RefKEquiv W Λ Ch sel mu cst hQ m2 Am u m2 := by
  intro g g' p p'
  have hmem : ∀ q' : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs, q'.1.y0 R.k ∈ ybSet sel mu cst q'.1.N :=
    fun q' => yOf_mem_ybSet sel mu cst hX hPr (pc_rowSG hQ) q' _
  have e : ∀ (q : ChPt (R := R) sel mu u m2) (q' : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) m2 q (liftQ hQ q') =
        cp1K W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
          (oneAl Λ sel mu m2 m2 (by omega)) q (liftQ hQ q') (q'.1.y0 R.k) := by
    intro q q'
    unfold refK cp1K
    rw [if_pos (show q'.1.y0 R.k ∈ ybSet sel mu cst (liftQ hQ q' : ChPt (R := R) sel mu u (m2 + 1)).deco.1.N from hmem q')]
    congr 1
    funext x
    unfold XiRef
    rw [dif_neg (lt_irrefl _), dif_pos rfl]
    rfl
  rw [e, e, lastVectorLine_equivariant hF, liftQ_oneG, liftQ_oneG]
  have h := h1 (oneAl Λ sel mu m2 m2 (by omega)) (oneG Λ sel mu g) (oneG Λ sel mu g') (liftQ hQ p) (liftQ hQ p') (p'.1.y0 R.k) (hmem p')
  refine h.trans ?_
  have h1' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g'
  have h2' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g⁻¹
  show (frmRho (colValF W sel mu u (m2 + 1)) (Λ (m2 + 1)) _ (oneG Λ sel mu g')) ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u m2) (Λ m2) _ (oneG Λ sel mu g)⁻¹) = _
  have h3 : (oneG Λ sel mu g)⁻¹ = oneG Λ sel mu g⁻¹ := by
    unfold oneG
    simp
  rw [h3, h1', h2']
  rfl

theorem refKEquiv_above {i : ℕ} (hi : m2 + 1 < i) : RefKEquiv W Λ Ch sel mu cst hQ m2 Am u i := by
  intro g g' p p'
  have e : ∀ (q : ChPt (R := R) sel mu u i) (q' : ChPt (R := R) sel mu u (i + 1)),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i q q' = 0 := by
    intro q q'
    unfold refK
    refine kerOf_zero _ _ _ _ _ _ _ _ _ fun x => ?_
    unfold XiRef
    rw [dif_neg (by omega), dif_neg (by omega), if_neg (by omega)]
  rw [e, e]
  ext x
  exact (map_zero (formRho (colVal W u (i + 1) (Pr.vT u) Pr.vGs) (Λ (i + 1)) g')).symm ▸ rfl

end Eq

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQRec
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QRec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
variable (H : Subgroup (GLG E n SG))

theorem qdf_ptOfF_spec (q : QLoc hc n Q Θ) (hSF : DecoPtSurjF hc n ST SG Q q) (p : DecoF E n ST SG Q) :
    FrOver q (ptOfF hc n ST SG Q q p).1 p := by
  unfold ptOfF
  rw [dif_pos (hSF p)]
  exact (hSF p).choose_spec

theorem qdf_levUQ_le_UAd (q : QLoc hc n Q Θ) : levUQ hc n ST SG Q H q ≤ UAd hc n := by
  unfold levUQ
  exact inf_le_left.trans (levU_le_UAd ..)

theorem qdf_mk_eq (q : QLoc hc n Q Θ) {x y : UAd hc n} (γ : URat hc n) (k : levUQ hc n ST SG Q H q)
    (e : (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) *
        (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) :
    (Quotient.mk'' y : Formalism.L2.DIV.Cl hc (1 : Matrix (Fin n) (Fin n) E) (levUQ hc n ST SG Q H q)) = Quotient.mk'' x := by
  have hk : ((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ ∈ UAd hc n :=
    qdf_levUQ_le_UAd H q (Subgroup.inv_mem _ k.2)
  refine Quotient.sound (DoubleCoset.rel_iff.2 ⟨(Formalism.L2.DIV.ratEl γ : UAd hc n), (Formalism.L2.DIV.ratEl γ).2, ⟨_, hk⟩,
    Subgroup.mem_subgroupOf.2 (Subgroup.inv_mem _ k.2), ?_⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact e

def qdStab (p : DecoF E n ST SG Q) : MulAction.stabilizer (UF E n × H × Θ.grp) p →* URat hc n :=
  (ratEquiv hc n).symm.toMonoidHom.comp ((MonoidHom.fst (UF E n) (H × Θ.grp)).comp (Subgroup.subtype _))

theorem qdf_ratHom_stab (p : DecoF E n ST SG Q) (a : MulAction.stabilizer (UF E n × H × Θ.grp) p) :
    ratHom hc n (qdStab H p a) = a.1.1 := by
  show ratEquiv hc n ((ratEquiv hc n).symm a.1.1) = a.1.1
  exact MulEquiv.apply_symm_apply _ _

theorem qdf_stab_deco (p : DecoF E n ST SG Q) (a : MulAction.stabilizer (UF E n × H × Θ.grp) p) :
    ((a.1.1, a.1.2.1) : UF E n × H) ∈ MulAction.stabilizer (UF E n × H) p.deco := by
  have h := congrArg DecoF.deco (MulAction.mem_stabilizer_iff.1 a.2)
  exact MulAction.mem_stabilizer_iff.2 h

theorem qdf_stab_fr (p : DecoF E n ST SG Q) (a : MulAction.stabilizer (UF E n × H × Θ.grp) p) (P : Q) :
    (a.1.2.2.1 P).1 = (p.fr P)⁻¹ * a.1.1.1 * p.fr P := by
  have h : (a.1 • p).fr P = p.fr P := congrArg (fun x : DecoF E n ST SG Q => x.fr P) (MulAction.mem_stabilizer_iff.1 a.2)
  change a.1.1.1 * p.fr P * ((a.1.2.2.1 P).1)⁻¹ = p.fr P at h
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

variable {H}

def recClsF (q : QLoc hc n Q Θ) (hSF : DecoPtSurjF hc n ST SG Q q) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q)
    (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q) (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c) :
    RecClsF hc n ST SG Q H q s where
  y c := ptOfF hc n ST SG Q q (s c)
  y_bij := by
    constructor
    · intro c c' h
      have hr := Quotient.exact' h
      obtain ⟨h0, hh, k, hk, e⟩ := DoubleCoset.rel_iff.1 hr
      obtain ⟨γ, hγ⟩ := Formalism.L2.DIV.ratEl_surjective (⟨h0, hh⟩ : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E))
      have hh' : ((h0 : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) :=
        (congrArg (fun z : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E) =>
          ((z : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) hγ).symm
      have hk' : ((k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ levUQ hc n ST SG Q H q :=
        Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hk)
      have e' : ((ptOfF hc n ST SG Q q (s c') : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (((⟨_, hk'⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ := by
        have e2 := congrArg (fun z : UAd hc n => (z : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) e
        simp only [Subgroup.coe_mul] at e2
        rw [e2, hh', inv_inv]
      obtain ⟨a, -, -, ha⟩ := qdf_orbit_of_rel H q (qdf_ptOfF_spec q hSF (s c)) (qdf_ptOfF_spec q hSF (s c')) γ ⟨_, hk'⟩ e'
      rw [← hs c, ← hs c']
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨a⁻¹, by show a⁻¹ • s c' = s c; rw [ha, inv_smul_smul]⟩)
    · intro Qc
      induction Qc using Quotient.inductionOn' with
      | h x =>
        obtain ⟨p, hp⟩ := qdf_over_exists q hF hE x
        refine ⟨Quotient.mk'' p, ?_⟩
        obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.1 (Quotient.exact (hs (Quotient.mk'' p)))
        have ha' : a • p = s (Quotient.mk'' p) := ha
        have hx' : FrOver q (ptOfF hc n ST SG Q q (s (Quotient.mk'' p))).1 (a • p) := by
          rw [ha']; exact qdf_ptOfF_spec q hSF _
        obtain ⟨γ, κ, -, e⟩ := qdf_rel_of_orbit H q a hp hx'
        exact (qdf_mk_eq H q γ κ e).symm
  y_lat c x := by
    have h := decoRaw_carries hc n ST SG (ptOfF hc n ST SG Q q (s c)).2 x
    rw [← rlc_decoOf_val hc n ST SG (ptOfF hc n ST SG Q q (s c)).2, (qdf_ptOfF_spec q hSF (s c)).1] at h
    exact h
  stabI c := qdStab H (s c)
  stabI_inj c := by
    intro a b hab
    have h1 : a.1.1 = b.1.1 := by rw [← qdf_ratHom_stab (hc := hc) H (s c) a, ← qdf_ratHom_stab (hc := hc) H (s c) b, hab]
    have ha := qdf_stab_deco H (s c) a
    have hb := qdf_stab_deco H (s c) b
    have hab' : ((a.1.1, (a.1.2.1 : GLG E n SG)) : UF E n × GLG E n SG) • (s c).deco = (s c).deco := ha
    have hbb' : ((b.1.1, (b.1.2.1 : GLG E n SG)) : UF E n × GLG E n SG) • (s c).deco = (s c).deco := hb
    have h2 := DecoSet.stab_fst_injective (s c).deco hab' hbb' h1
    have h3 : a.1.2.2 = b.1.2.2 := by
      apply Subtype.ext
      funext P
      apply Subtype.ext
      rw [qdf_stab_fr H (s c) a P, qdf_stab_fr H (s c) b P, h1]
    exact Subtype.ext (Prod.ext h1 (Prod.ext (Subtype.ext (congrArg Prod.snd h2)) h3))
  stabI_range c γ hγ := by
    constructor
    · rintro ⟨a, ha⟩
      have hx := qdf_ptOfF_spec q hSF (s c)
      have hx' : FrOver q (ptOfF hc n ST SG Q q (s c)).1 (a.1 • s c) := by rw [a.2]; exact hx
      obtain ⟨γ', κ, h1, e⟩ := qdf_rel_of_orbit H q a.1 hx hx'
      have hγ' : γ' = ⟨γ, hγ⟩ := by
        rw [← ha]
        exact (ratHom_bijective hc n).1 (h1.trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
      refine ⟨κ.1, κ.2, ?_⟩
      show ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * κ.1 *
        ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ = _
      have e' : Formalism.UG.bc (iA F E) (γ' : GL (Fin n) E) = ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          κ.1 * ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ :=
        eq_mul_inv_of_mul_eq (eq_mul_inv_iff_mul_eq.1 e).symm
      rw [← e', hγ']
    · rintro ⟨k, hk, e⟩
      have e' : ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k *
          ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) := e
      have e2 : ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) *
            ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            ((⟨k, hk⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
        rw [← e']; group
      obtain ⟨a, ha1, -, ha⟩ := qdf_orbit_of_rel H q (qdf_ptOfF_spec q hSF (s c)) (qdf_ptOfF_spec q hSF (s c)) ⟨γ, hγ⟩ ⟨k, hk⟩ e2
      refine ⟨⟨a, ha.symm⟩, ?_⟩
      apply (ratHom_bijective hc n).1
      rw [qdf_ratHom_stab (hc := hc) H (s c) ⟨a, ha.symm⟩, ha1]
  stabI_lat c a x := by
    have h := stabRat_lat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ x
    have e : stabRat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ = qdStab H (s c) a :=
      (ratHom_bijective hc n).1 ((rlc_ratHom_stabRat hc n ST SG H _ _).trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
    rw [e] at h
    exact h

end QRec

end Formalism.L2.Col
end
end

