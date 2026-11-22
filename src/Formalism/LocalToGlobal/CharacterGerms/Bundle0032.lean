import Formalism.LocalToGlobal.CharacterGerms.Bundle0028
import Formalism.LocalToGlobal.CharacterGerms.Bundle0021
import Formalism.LocalToGlobal.CharacterGerms.Bundle0009
import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
import Formalism.LocalToGlobal.CharacterGerms.Bundle0019
import Formalism.LocalToGlobal.CharacterGerms.Bundle0029
import Formalism.LocalToGlobal.CharacterGerms.Bundle0001
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDelta
import Formalism.LocalToGlobal.CharacterGerms.Bundle0003

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieMemCHarm
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem letter_cast {T : Type} {r : T → ℕ} {n : ℕ} {σ σ' : T} (h : σ = σ') (a : Fin (r σ)) :
    ∃ a' : Fin (r σ'), ∀ b : Fin n, (⟨σ, a, b⟩ : Letter T r n) = ⟨σ', a', b⟩ := by
  subst h
  exact ⟨a, fun b => rfl⟩

section Plane

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem lap_plane (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) (o : Orb) (t : ZMod 2)
    (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + 1))))
    (hno : ∀ ρ g1 g2, g1 ≠ g2 → (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ Q.vars →
      (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars → False) :
    ∑ b, pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
      (subG r tau gm plc Q)) = 0 := by
  have hoff : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ∉ Finset.univ.map plc →
      pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
        (subG r tau gm plc Q)) = 0 := by
    intro b _ hb
    rw [pderiv_subG_off plc (ℓ := ⟨tau o (t + 1), a2, b⟩), map_zero]
    intro z e
    apply hb
    rw [Finset.mem_map]
    exact ⟨(z.1.1, z.2), Finset.mem_univ _, (congrArg (fun ℓ : Letter T r n => ℓ.2.2) e).symm⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map plc)) hoff, Finset.sum_map, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have hf : ∀ col, pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n)
      (pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q)) =
      ∑ g1, ∑ g2, MvPolynomial.C (gm o t col g1 * gm o (t + 1) col g2) *
        subG r tau gm plc (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
          (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) := by
    intro col
    have e2 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t + 1, a2⟩⟩) : AA r tau N) col Q
    have e2' : pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q) = _ := e2
    rw [e2', map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g2 _ => ?_
    rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
    have e1 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t, a1⟩⟩) : AA r tau N) col
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)
    have e1' : pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) = _ := e1
    rw [e1', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g1 _ => ?_
    rw [map_mul]
    unfold Gm
    ring
  simp only [hf]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g2 _ => ?_
  rw [← Finset.sum_mul, ← map_sum]
  by_cases hg : g1 = g2
  · have hK : ∑ col, gm o t col g1 * gm o (t + 1) col g2 = 0 := by
      have h := gm_hyp o t g2 g1
      rw [if_pos hg.symm] at h
      rw [← h]
      exact Finset.sum_congr rfl fun q _ => mul_comm _ _
    rw [hK, map_zero, zero_mul]
  · have hz : pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
        (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q) = 0 := by
      by_cases h2 : (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars
      · have h1 : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∉ Q.vars := fun h1 => hno ρ g1 g2 hg h1 h2
        rw [pderiv_comm', pderiv_eq_zero_of_notMem_vars h1, map_zero]
      · rw [pderiv_eq_zero_of_notMem_vars h2, map_zero]
    rw [hz, map_zero, mul_zero]

end Plane

section Fam

theorem mem_vars_blkProdG {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (I o) (J o)} {F : ∀ o, Flag (X o)} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n} {b : Fin n} {o : Orb} {w : WV (I o)}
    (hx : ((b, ⟨o, w⟩) : Fin n × WVO I) ∈ (blkProd X F n L pl).vars) :
    (b, w) ∈ (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)).vars := by
  first
  | unfold blkProd at hx
  | simp only [blkProd] at hx
  first
  | unfold toAll at hx
  | simp only [toAll] at hx
  have h1 := MvPolynomial.vars_prod _ hx
  rw [Finset.mem_biUnion] at h1
  obtain ⟨o', -, h2⟩ := h1
  have h3 := MvPolynomial.vars_rename _ _ h2
  rw [Finset.mem_image] at h3
  obtain ⟨x, hx1, hx2⟩ := h3
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at hx2
  obtain ⟨hb, ho, hw⟩ := hx2
  subst ho
  obtain rfl := eq_of_heq hw
  subst hb
  exact hx1

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}

theorem zmod_two_add_one_add_one_eq : ∀ t : ZMod 2, t + 1 + 1 = t := by
  decide

theorem SelfConjugatePlaceSetting.rowsOK (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) :
    ∃ kind : Fin N → Knd 2, RowsOK (X o).G (X o).Alt
      (prodAll (plAt N pl o) fun i => (blkAt L o i).poly (X o) (F o)) kind := by
  have h : ∀ i : Fin (L o).length, ∃ kind : Fin (rowsAt X L o i) → Knd 2,
      RowsOK (X o).G (X o).Alt ((blkAt L o i).poly (X o) (F o)) kind := by
    intro i
    refine exists_rowsOK (X o) (F o) (Or.inl (H.alt o)) (H.hj o) _ fun g t k hk => ?_
    have hsum : ∀ s, (blkAt L o i).wt (X o) 0 s k + (blkAt L o i).wt (X o) 1 (s + 1) k ≤ gaC o s k := by
      intro s
      rw [← H.wt o s k]
      exact le_sum_map (L o) (fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k) (List.get_mem (L o) i)
    by_cases hg : g = 0
    · subst hg
      have h1 := hsum t
      exact (H.supp o t k (by omega)).2
    · have hg1 : g = 1 := Fin.eq_one_of_ne_zero g hg
      subst hg1
      have h1 := hsum (t + 1)
      rw [zmod_two_add_one_add_one_eq] at h1
      have h2 := (H.supp o (t + 1) k (by omega)).2
      rw [H.rkF_eq o 0 (t + 1)] at h2
      rw [H.rkF_eq o 1 t]
      exact h2
  choose kind hk using h
  exact ⟨_, rowsOK_prodAll _ _ (plAt_inj N H.plinj o) _ kind hk⟩

theorem lab_eq : ∀ g1 g2 : Fin 2, g1 ≠ g2 → ∀ t : ZMod 2,
    (if g1 = 0 then t else t + 1) = (if g2 = 0 then t + 1 else t + 1 + 1) := by
  decide

theorem SelfConjugatePlaceSetting.no_conj (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (ρ : Fin N) (o : Orb) (g1 g2 : Fin 2) (hne : g1 ≠ g2)
    (t : ZMod 2) (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + 1))))
    (hx : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ (blkProd X F N L pl).vars)
    (hx' : (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ (blkProd X F N L pl).vars) : False := by
  obtain ⟨kind, hk⟩ := H.rowsOK o
  have hx1 : ((ρ, ⟨o, ⟨g1, ⟨t, a1⟩⟩⟩) : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ∈ (blkProd X F N L pl).vars := hx
  have hx2 : ((ρ, ⟨o, ⟨g2, ⟨t + 1, a2⟩⟩⟩) : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ∈ (blkProd X F N L pl).vars := hx'
  have h1 := mem_vars_blkProdG hx1
  have h2 := mem_vars_blkProdG hx2
  have ht : tyW (X o).G (⟨g1, ⟨t, a1⟩⟩ : WV fun _ => IIs r tau o) = tyW (X o).G (⟨g2, ⟨t + 1, a2⟩⟩ : WV fun _ => IIs r tau o) :=
    (H.hty o g1 ⟨t, a1⟩).trans ((lab_eq g1 g2 hne t).trans (H.hty o g2 ⟨t + 1, a2⟩).symm)
  exact no_conj_of_rowsOK hk h1 h2 hne ht

end Fam

theorem isotropic_to_std_subst_harmonic : IsotropicToStdSubstHarmonic := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc isX
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ _ a1 a2
  rw [lap_one_apply]
  have hdiag : ∀ b, (∑ b', (1 : Matrix (Fin n) (Fin n) C) b b' •
      pderiv (⟨τ, a1, b⟩ : Letter T r n) (pderiv (⟨cc τ, a2, b'⟩ : Letter T r n)
        (subG r tau gm plc (blkProd X F N L pl)))) =
      pderiv (⟨τ, a1, b⟩ : Letter T r n) (pderiv (⟨cc τ, a2, b⟩ : Letter T r n)
        (subG r tau gm plc (blkProd X F N L pl))) := by
    intro b
    rw [Finset.sum_eq_single b]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro b' _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hdiag]
  by_cases hτ : ∃ o t, tau o t = τ
  · obtain ⟨o, t, rfl⟩ := hτ
    obtain ⟨a2', ha2⟩ := letter_cast (n := n) (H.conj o t) a2
    simp only [ha2]
    exact lap_plane plc H.inj H.gm_hyp _ o t a1 a2' fun ρ g1 g2 hne h1 h2 => H.no_conj ρ o g1 g2 hne t a1 a2' h1 h2
  · push Not at hτ
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [pderiv_comm', pderiv_subG_off plc (ℓ := ⟨τ, a1, b⟩), map_zero]
    intro z e
    exact hτ _ _ (congrArg Sigma.fst e).symm

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePAllStart
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

namespace AllStart

variable {C : Type} [Field C]

theorem linAct_sum {dd : ℕ} (φ : Pt C 1 dd) {ι : Type} (S : Finset ι) (w : ι → C) (u : ι → Fin dd → C) :
    linAct φ (∑ c ∈ S, w c • u c) = ∑ c ∈ S, w c • linAct φ (u c) := by
  funext i
  simp only [linAct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

theorem coeff_one_subst {dd : ℕ} (f : PS C 1 dd)
    (hf : ∀ (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ f = 0)
    (P : Fin 1 × Fin dd → PowerSeries C) (hP0 : ∀ q, MvPowerSeries.constantCoeff (P q) = 0) :
    MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.subst P f) = 0 := by
  have hA : MvPowerSeries.HasSubst P := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  rw [MvPowerSeries.coeff_subst hA]
  refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
  by_cases hμ : μ.degree ≤ 1
  · rw [hf μ hμ, zero_smul]
  · push_neg at hμ
    have hX : ∀ q, (PowerSeries.X : PowerSeries C) ∣ P q := fun q => PowerSeries.X_dvd_iff.2 (hP0 q)
    have hdeg : μ.degree = ∑ s ∈ μ.support, μ s := rfl
    have h1 : (PowerSeries.X : PowerSeries C) ^ μ.degree ∣ μ.prod fun s e => P s ^ e := by
      rw [hdeg, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun s _ => pow_dvd_pow_of_dvd (hX s) _
    have hdvd : (PowerSeries.X : PowerSeries C) ^ 2 ∣ μ.prod fun s e => P s ^ e := (pow_dvd_pow _ hμ).trans h1
    have h2 := (PowerSeries.X_pow_dvd_iff.1 hdvd) 1 (by norm_num)
    rw [show MvPowerSeries.coeff (Finsupp.single () 1) (μ.prod fun s e => P s ^ e) = 0 from h2, smul_zero]

end AllStart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem allStart_of_proj (Y : FBChart C V O dd) (p : PairData Y d I) (hP : ProjSt Y p) (g : Fin 2) (w : I g → C)
    (hw : ∀ c, V.Ge 0 (w c)) : ∃ L ∈ (Y.raw p).AllSet V g, ∀ c, L 1 (Sum.inl c) = w c := by
  obtain ⟨e, heI, he0, hhom, -, -, hfix, hspan, -⟩ := hP
  let v : Fin dd → C := ∑ c, w c • p.u g c
  have hvI : ∀ j, V.Ge 0 (v j) := fun j => by
    simp only [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact VF.Ge.sum fun c _ => (hw c).mul_int (p.u_int g c j)
  let P : Fin 1 × Fin dd → PowerSeries C := fun q =>
    MvPowerSeries.C (v q.2) * MvPowerSeries.X ()
  have hP0 : ∀ q, MvPowerSeries.constantCoeff (P q) = 0 := fun q => by
    simp [P]
  have hPI : ∀ q, IntS V (P q) := fun q μ => by
    simp only [P, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    split_ifs
    · rw [mul_one]; exact hvI q.2
    · rw [mul_zero]; exact VF.Ge.zero 0
  have hPS := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  let a : ℕ → Fin dd → C := fun n j => PowerSeries.coeff n (MvPowerSeries.subst P (Y.lg j))
  have ha1 : ∀ j, a 1 j = v j := fun j => by
    show MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.subst P (Y.lg j)) = v j
    have e1 : Y.lg j = MvPowerSeries.X ((0 : Fin 1), j) + (Y.lg j - MvPowerSeries.X ((0 : Fin 1), j)) := by ring
    have h0 := AllStart.coeff_one_subst (Y.lg j - MvPowerSeries.X ((0 : Fin 1), j))
      (fun μ hμ => by rw [map_sub, Y.lg_lin j μ hμ, sub_self]) P hP0
    rw [e1, MvPowerSeries.subst_add hPS, MvPowerSeries.subst_X hPS, map_add, h0, add_zero]
    simp [P, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  have hv : linAct (e g) v = v := by
    show linAct (e g) (∑ c, w c • p.u g c) = ∑ c, w c • p.u g c
    rw [AllStart.linAct_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [hfix g c]
  let b : ℕ → I g → C := fun n => Classical.choose (hspan g (a n))
  have hb : ∀ n, linAct (e g) (a n) = ∑ c, b n c • p.u g c := fun n => Classical.choose_spec (hspan g (a n))
  let Linl : ℕ → I g → C := fun n c => if n = 1 then w c else b n c
  have hkey : ∀ n i, ∑ j, OActLog.linM (e g) i j * a n j = ∑ c, p.u g c i * Linl n c := by
    intro n i
    have hl : ∑ j, OActLog.linM (e g) i j * a n j = linAct (e g) (a n) i := rfl
    rw [hl]
    by_cases hn : n = 1
    · subst hn
      have e2 : a 1 = v := funext ha1
      rw [e2, hv]
      simp only [Linl, if_pos rfl, v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    · rw [hb n]
      simp only [Linl, if_neg hn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  let γ : Fin dd → PowerSeries C := fun i => MvPowerSeries.subst P (e g i)
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := fun i => constantCoeff_subst_zero hP0 (he0 g i)
  have hγ : IsCv V γ := fun i => ⟨hγ0 i, fun n => IntS.subst hP0 hPI (heI g i) (Finsupp.single () n)⟩
  have heS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => e g q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => he0 g q.2
  have hlog : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c, (Y.raw p).u g c i • PowerSeries.mk (fun n => Linl n c) := by
    intro i
    have h1 : alongCv γ ((Y.raw p).lg i) = MvPowerSeries.subst P (comp1 Y.lg (e g) i) := by
      show MvPowerSeries.subst γ (un1 (Y.lg i)) = _
      rw [subst_singlePointUncurry hγ0]
      show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst P (e g q.2)) (Y.lg i) =
        MvPowerSeries.subst P (ev ![e g] (Y.lg i))
      rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply heS hPS]
    rw [h1, OActLog.log_endo Y.B.G Y.lg Y.lg_lin Y.lg_add (e g) (he0 g) (hhom g) i]
    simp only [← MvPowerSeries.smul_eq_C_mul]
    rw [← MvPowerSeries.coe_substAlgHom hPS, map_sum]
    simp only [map_smul, MvPowerSeries.coe_substAlgHom hPS]
    refine PowerSeries.ext fun n => ?_
    simp only [map_sum, map_smul, smul_eq_mul, PowerSeries.coeff_mk]
    exact hkey n i
  let RHS : JJ I g → PowerSeries C := fun q =>
    (0 : PowerSeries C) - alongCv γ ((Y.raw p).sg ((Y.raw p).u (1 - g) q)) +
      ∑ c : I g, if (Y.raw p).ty g c = (Y.raw p).ty (1 - g) q then
        (Y.raw p).sg1 ((Y.raw p).u g c) ((Y.raw p).u (1 - g) q) • PowerSeries.mk (fun n => Linl n c) else 0
  let L : ℕ → I g ⊕ JJ I g → C := fun n k => Sum.elim (fun c => Linl n c) (fun q => PowerSeries.coeff n (RHS q)) k
  refine ⟨L, ⟨γ, fun _ => 0, hγ, fun q => ⟨by simp, fun n => by simpa using VF.Ge.zero (V := V) 0⟩, hlog, ?_⟩, ?_⟩
  · intro q
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_mk]
    rfl
  · intro c
    show (if 1 = 1 then w c else b 1 c) = w c
    rw [if_pos rfl]

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigB
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey RowTiePProj GmExArith

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n d : ℕ} (K : KeyData C V O n d)

theorem em_iter (x : O) (a : ZMod d) (k : ℕ) : V.MM (K.em (a + k) x - K.em a x ^ V.l ^ k) := by
  induction k with
  | zero => simp [mm_zero]
  | succ k ih =>
    have h1 := K.em_frob (a + k) x
    have h2 := mm_pow_sub (K.em_int _ x) ((K.em_int a x).pow _) ih V.l
    have e : K.em (a + ((k + 1 : ℕ) : ZMod d)) x - K.em a x ^ V.l ^ (k + 1) =
        (K.em (a + k + 1) x - K.em (a + k) x ^ V.l) + (K.em (a + k) x ^ V.l - (K.em a x ^ V.l ^ k) ^ V.l) := by
      rw [← pow_mul, ← pow_succ, Nat.cast_succ, ← add_assoc]; ring
    rw [e]
    exact mm_add h1 h2

theorem em_cong (x : O) (a : ZMod d) : V.MM (K.em a (x ^ V.l ^ d - x)) := by
  have h := em_iter K x a d
  rw [ZMod.natCast_self, add_zero] at h
  rw [map_sub, map_pow]
  have := mm_neg h
  rwa [neg_sub] at this

theorem star_S (x : O) : (V.l : C)⁻¹ • ((K.P * K.ρ x) ^ V.l ^ d - K.P * K.ρ x) ∈ Acl K := by
  obtain ⟨y, hy⟩ := K.ε_ann (x ^ V.l ^ d - x) fun a => em_cong K x a
  have hl0 : (V.l : C) ≠ 0 := V.l_ne_zero
  have hq : V.l ^ d = (V.l ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero _ V.l_prime.ne_zero))).symm
  have eM : (K.P * K.ρ x) ^ V.l ^ d - K.P * K.ρ x = K.P * (K.P * K.ρ (x ^ V.l ^ d - x)) := by
    rw [← Matrix.mul_assoc, P_idem, map_sub, Matrix.mul_sub, hq, S_pow, ← hq]
  rw [eM]
  refine ⟨fun k => K.ε ^ (V.l ^ k - 1) * y, ?_⟩
  have key : ∀ k : ℕ, K.P * K.ρ (K.ε ^ (V.l ^ k - 1) * y) =
      (V.l : C)⁻¹ • (K.ρ (K.ε ^ V.l ^ k) * (K.P * K.ρ (x ^ V.l ^ d - x))) := by
    intro k
    have hk : V.l ^ k ≠ 0 := pow_ne_zero _ V.l_prime.ne_zero
    have e1 : K.ε ^ V.l ^ k * (x ^ V.l ^ d - x) = (V.l : O) * (K.ε ^ (V.l ^ k - 1) * y) := by
      rw [← pow_sub_one_mul hk, mul_assoc, hy]; ring
    rw [← Matrix.mul_assoc, ← P_comm, Matrix.mul_assoc, ← map_mul, e1, ρ_natmul, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hl0, one_smul]
  have hseq : (fun k => K.P * K.ρ (K.ε ^ (V.l ^ k - 1) * y)) =
      fun k => (V.l : C)⁻¹ • (K.ρ (K.ε ^ V.l ^ k) * (K.P * K.ρ (x ^ V.l ^ d - x))) := funext key
  rw [hseq]
  exact MT.smul _ ((hPT K).mul (MT.const _))

theorem star_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) : (V.l : C)⁻¹ • (B ^ V.l ^ d - B) ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  exact closed_mem K (fun k => star_S K (s k)) (MT.smul _ ((hs.pow _).sub hs))

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTop
section
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

theorem projFB_of_eig_res (hE : KeyEigSt) (hR : KeyResSt) : ProjFBSt :=
  RowTiePProj.projFB_of_lie (RowTiePLie.projLie_of (key_of hE hR keyDelta_holds) RowTiePSplit.split_holds)

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end

