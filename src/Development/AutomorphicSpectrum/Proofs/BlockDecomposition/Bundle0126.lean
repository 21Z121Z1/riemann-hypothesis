import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Transp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirrorPartitions
section
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin PI.GreenLabelSurjWork

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.Mirrors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

theorem cuspIso_symm {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} (h : CuspIso K lam mu) :
    CuspIso K mu lam := by
  obtain ⟨e, φ⟩ := id h
  exact (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α β β lam lam mu mu e).1 h

theorem cuspIso_trans {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} {nu : FDRep ℂ (GL γ K)}
    (h : CuspIso K lam mu) (h' : CuspIso K mu nu) : CuspIso K lam nu := by
  obtain ⟨e, φ⟩ := id h
  exact (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α β γ lam lam mu nu e).2.1 h h'

theorem cuspIso_of_iso {lam lam' : FDRep ℂ (GL α K)} (h : Nonempty (lam ≅ lam')) :
    CuspIso K lam lam' :=
  (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α α α lam lam' lam lam (Equiv.refl α)).2.2.1 h

theorem cuspIso_transp (e : α ≃ β) (lam : FDRep ℂ (GL α K)) : CuspIso K lam (transp e lam) :=
  (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α β β lam lam (transp e lam) (transp e lam) e).2.2.2.1

theorem cuspIso_iff_transp (e : α ≃ β) {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)}
    (hl : Simple lam) (hm : Simple mu) : CuspIso K lam mu ↔ Nonempty (transp e lam ≅ mu) :=
  (GlobalTheory.CompanionTheory.TyFin.IpIso.main K α β lam mu e hl hm).2

theorem lab_cast (O : LabelMap K C) {a b : ℕ} (h : a = b) (X : FDRep ℂ (GL (Fin a) K))
    (hX : Simple X) : O.lab b (transp (finCongr h) X) = O.lab a X := by
  subst h
  exact O.lab_iso _ _ _ ((cuspIso_iff_transp (finCongr rfl) hX hX).1 (cuspIso_of_iso ⟨Iso.refl X⟩))

theorem lab_eq_of_cuspIso (O : LabelMap K C) {a b : ℕ} {X : FDRep ℂ (GL (Fin a) K)}
    {Y : FDRep ℂ (GL (Fin b) K)} (hX : Simple X) (hY : Simple Y) (h : CuspIso K X Y) :
    O.lab a X = O.lab b Y := by
  obtain ⟨e, φ⟩ := id h
  have hab : a = b := by simpa using Fintype.card_congr e
  rw [← lab_cast O hab X hX]
  exact O.lab_iso b _ _ ((cuspIso_iff_transp (finCongr hab) hX hY).1 h)

theorem labO_transp (O : LabelMap K C) {d : ℕ} (e : Fin d ≃ β) {σ : FDRep ℂ (GL (Fin d) K)}
    (hσ : Simple σ) : labO O (transp e σ) = O.lab d σ :=
  (lab_eq_of_cuspIso O hσ (transp_simple _ _ (transp_simple _ _ hσ))
    (cuspIso_trans (cuspIso_transp e σ) (cuspIso_transp (Fintype.equivFin β) (transp e σ)))).symm

theorem labO_eq_of_cuspIso (O : LabelMap K C) {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)}
    (hl : Simple lam) (hm : Simple mu) (h : CuspIso K lam mu) : labO O lam = labO O mu :=
  lab_eq_of_cuspIso O (transp_simple _ _ hl) (transp_simple _ _ hm)
    (cuspIso_trans (cuspIso_symm (cuspIso_transp _ lam)) (cuspIso_trans h (cuspIso_transp _ mu)))

theorem cuspIso_of_labO_eq (O : LabelMap K C) [Nonempty α] [Nonempty β] {lam : FDRep ℂ (GL α K)}
    {mu : FDRep ℂ (GL β K)} (hl : Simple lam) (hlc : IsCuspidal K lam) (hm : Simple mu)
    (hmc : IsCuspidal K mu) (h : labO O lam = labO O mu) : CuspIso K lam mu := by
  have sX := transp_simple (Fintype.equivFin α) lam hl
  have cX := transp_cusp (Fintype.equivFin α) lam hlc
  have sY := transp_simple (Fintype.equivFin β) mu hm
  have cY := transp_cusp (Fintype.equivFin β) mu hmc
  have dα := (O.lab_spec _ _ Fintype.card_pos sX cX).2.2.2
  have dβ := (O.lab_spec _ _ Fintype.card_pos sY cY).2.2.2
  have hab : Fintype.card α = Fintype.card β := by
    rw [← dα, ← dβ]
    exact congrArg Polynomial.natDegree h
  have h' : O.lab _ (transp (finCongr hab) (transp (Fintype.equivFin α) lam)) =
      O.lab _ (transp (Fintype.equivFin β) mu) := by
    rw [lab_cast O hab _ sX]
    exact h
  have hi := O.lab_inj _ _ _ Fintype.card_pos (transp_simple _ _ sX) (transp_cusp _ _ cX) sY cY h'
  exact cuspIso_trans (cuspIso_transp _ lam) (cuspIso_trans (cuspIso_transp (finCongr hab) _)
    (cuspIso_trans (cuspIso_of_iso hi) (cuspIso_symm (cuspIso_transp _ mu))))

theorem labO_eq_iff (O : LabelMap K C) [Nonempty α] [Nonempty β] {lam : FDRep ℂ (GL α K)}
    {mu : FDRep ℂ (GL β K)} (hl : Simple lam) (hlc : IsCuspidal K lam) (hm : Simple mu)
    (hmc : IsCuspidal K mu) : labO O lam = labO O mu ↔ CuspIso K lam mu :=
  ⟨cuspIso_of_labO_eq O hl hlc hm hmc, labO_eq_of_cuspIso O hl hm⟩

theorem fiber_nonempty {ι : Type} {s : ℕ} {b : ι → Fin s} (hb : Function.Surjective b) (c : Fin s) :
    Nonempty {i // b i = c} :=
  let ⟨i, hi⟩ := hb c
  ⟨⟨i, hi⟩⟩

theorem hcLabelO (hE : HC.HCSupportExists K) (hU : SupportUnique K) (O : LabelMap K C) :
    HCLabelO O := by
  intro n hn τ hτ
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · obtain ⟨s, b, lam, hb, hl, hc⟩ := hE τ hτ
    exact ⟨_, s, b, lam, hb, hl, hc, rfl⟩
  · rintro f f' ⟨s, b, lam, hb, hl, hc, rfl⟩ ⟨s', b', mu, hb', hl', hc', rfl⟩
    obtain ⟨π, hπ⟩ := hU n s s' b b' lam mu τ hτ ⟨hb, hl, hc⟩ ⟨hb', hl', hc'⟩
    rw [Finset.prod_congr rfl (fun c _ => labO_eq_of_cuspIso O (hl c).1 (hl' _).1 (hπ c))]
    exact Equiv.prod_comp π (fun c => labO O (mu c))

theorem labelSurjO (O : LabelMap K C) (hC : CuspParamO O) : LabelSurjO O := by
  classical
  intro n hn f hfm hfn hf0
  have hf0' : f ≠ 0 := hfm.ne_zero
  let L := (UniqueFactorizationMonoid.normalizedFactors f).toList
  let s := L.length
  let P : Fin s → K[X] := fun c => L.get c
  have hmem : ∀ c, P c ∈ UniqueFactorizationMonoid.normalizedFactors f := fun c =>
    Multiset.mem_toList.mp (List.get_mem L c)
  have hirr : ∀ c, Irreducible (P c) := fun c =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor _ (hmem c)
  have hmon : ∀ c, (P c).Monic := fun c => by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor _ (hmem c)]
    exact Polynomial.monic_normalize (hirr c).ne_zero
  have hX : ∀ c, P c ≠ X := fun c h => hf0 (Polynomial.X_dvd_iff.mp
    (h ▸ UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (hmem c)))
  have hprod : ∏ c, P c = f := by
    rw [show ∏ c, P c = L.prod by rw [← List.prod_ofFn]; exact congrArg List.prod (List.ofFn_get L)]
    rw [Multiset.prod_toList, UniqueFactorizationMonoid.prod_normalizedFactors_eq hf0',
      hfm.normalize_eq_self]
  let d : Fin s → ℕ := fun c => (P c).natDegree
  have hd : ∀ c, 1 ≤ d c := fun c =>
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible (hirr c))
  have hsum : ∑ c, d c = n := by
    rw [← Polynomial.natDegree_prod_of_monic _ _ (fun c _ => hmon c), hprod, hfn]
  let E : (Σ c : Fin s, Fin (d c)) ≃ Fin n := finSigmaFinEquiv.trans (finCongr hsum)
  let b : Fin n → Fin s := fun i => (E.symm i).1
  let e : ∀ c, Fin (d c) ≃ {i // b i = c} := fun c =>
    ((E.symm.subtypeEquiv (p := fun i => b i = c) (q := fun x => x.1 = c) (fun _ => Iff.rfl)).trans
      (Equiv.sigmaSubtype c)).symm
  have hb : Function.Surjective b := fun c => ⟨E ⟨c, ⟨0, hd c⟩⟩, by simp [b]⟩
  choose σ hσ using fun c => (hC (d c) (hd c)).1 (P c) (hmon c) (hirr c) (hX c) rfl
  let lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K) := fun c => transp (e c) (σ c)
  have hlam : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c) := fun c =>
    ⟨transp_simple _ _ (hσ c).1, transp_cusp _ _ (hσ c).2.1⟩
  haveI : Nontrivial (hcSpace K b lam) :=
    hcSpace_nontrivial b lam (fun c => nontrivial_of_simple _ (hlam c).1)
  obtain ⟨τ, hτ, hcon⟩ := exists_simple_constituent (hcRep K b lam)
  refine ⟨τ, hτ, s, b, lam, hb, hlam, hcon, ?_⟩
  rw [← hprod]
  exact Finset.prod_congr rfl fun c _ => by
    rw [show labO O (lam c) = O.lab (d c) (σ c) from labO_transp O (e c) (hσ c).1, (hσ c).2.2]

theorem injective_of_squarefree_prod {s : ℕ} {P : Fin s → K[X]} (hi : ∀ c, Irreducible (P c))
    (hf : Squarefree (∏ c, P c)) : Function.Injective P := by
  intro c c' h
  by_contra hne
  have hd : P c * P c ∣ ∏ x, P x := by
    have h1 := Finset.prod_dvd_prod_of_subset {c, c'} Finset.univ P (Finset.subset_univ _)
    rw [Finset.prod_pair hne, ← h] at h1
    exact h1
  exact (hi c).not_isUnit (hf _ hd)

theorem exists_factor_eq {s s' : ℕ} {P : Fin s → K[X]} {P' : Fin s' → K[X]}
    (hi : ∀ c, Irreducible (P c)) (hm : ∀ c, (P c).Monic) (hi' : ∀ c, Irreducible (P' c))
    (hm' : ∀ c, (P' c).Monic) (h : ∏ c, P c = ∏ c, P' c) (c : Fin s) : ∃ c', P' c' = P c := by
  have hd : P c ∣ ∏ x, P' x := h ▸ Finset.dvd_prod_of_mem P (Finset.mem_univ c)
  obtain ⟨c', -, hc'⟩ := (hi c).prime.exists_mem_finset_dvd hd
  exact ⟨c', Polynomial.eq_of_monic_of_associated (hm' c') (hm c)
    ((hi c).associated_of_dvd (hi' c') hc').symm⟩

theorem exists_equiv_factors {s s' : ℕ} {P : Fin s → K[X]} {P' : Fin s' → K[X]}
    (hi : ∀ c, Irreducible (P c)) (hm : ∀ c, (P c).Monic) (hi' : ∀ c, Irreducible (P' c))
    (hm' : ∀ c, (P' c).Monic) (hj : Function.Injective P) (hj' : Function.Injective P')
    (h : ∏ c, P c = ∏ c, P' c) : ∃ π : Fin s ≃ Fin s', ∀ c, P' (π c) = P c := by
  choose m hmP using exists_factor_eq hi hm hi' hm' h
  choose m' hmP' using exists_factor_eq hi' hm' hi hm h.symm
  have i1 : Function.Injective m := fun x y hxy => hj (by rw [← hmP x, ← hmP y, hxy])
  have i2 : Function.Injective m' := fun x y hxy => hj' (by rw [← hmP' x, ← hmP' y, hxy])
  have hcard : s = s' := le_antisymm (by simpa using Fintype.card_le_of_injective m i1)
    (by simpa using Fintype.card_le_of_injective m' i2)
  have bij : Function.Bijective m :=
    (Fintype.bijective_iff_injective_and_card m).2 ⟨i1, by simp [hcard]⟩
  exact ⟨Equiv.ofBijective m bij, hmP⟩

theorem labO_spec (O : LabelMap K C) [Nonempty α] {lam : FDRep ℂ (GL α K)} (hl : Simple lam)
    (hc : IsCuspidal K lam) : (labO O lam).Monic ∧ Irreducible (labO O lam) :=
  let h := O.lab_spec _ _ Fintype.card_pos (transp_simple (Fintype.equivFin α) lam hl)
    (transp_cusp (Fintype.equivFin α) lam hc)
  ⟨h.1, h.2.1⟩

theorem sqfreeO (hC : SqfreeCore K) (O : LabelMap K C) (hP : CuspParamO O) : SqfreeO O := by
  obtain ⟨hI, hD, hU⟩ := hC
  refine ⟨?_, ?_⟩
  · intro n s b lam hb hl hinj
    refine ⟨hI n s b lam hb hl fun c c' h => hinj (labO_eq_of_cuspIso O (hl c).1 (hl c').1 h), ?_⟩
    refine hD n s b lam hb fun c => ?_
    haveI := fiber_nonempty hb c
    exact (hP (Fintype.card {i // b i = c}) Fintype.card_pos).2
      (transp (Fintype.equivFin _) (lam c)) (transp_simple _ _ (hl c).1) (transp_cusp _ _ (hl c).2)
  · rintro n f τ τ' hf hτ hτ' ⟨s, b, lam, hb, hl, hc, rfl⟩ ⟨s', b', mu, hb', hl', hc', hf'⟩
    have sp : ∀ c, (labO O (lam c)).Monic ∧ Irreducible (labO O (lam c)) := fun c =>
      haveI := fiber_nonempty hb c
      labO_spec O (hl c).1 (hl c).2
    have sp' : ∀ c, (labO O (mu c)).Monic ∧ Irreducible (labO O (mu c)) := fun c =>
      haveI := fiber_nonempty hb' c
      labO_spec O (hl' c).1 (hl' c).2
    have hj : Function.Injective fun c => labO O (lam c) :=
      injective_of_squarefree_prod (fun c => (sp c).2) hf
    have hj' : Function.Injective fun c => labO O (mu c) :=
      injective_of_squarefree_prod (fun c => (sp' c).2) (hf' ▸ hf)
    obtain ⟨π, hπ⟩ := exists_equiv_factors (fun c => (sp c).2) (fun c => (sp c).1)
      (fun c => (sp' c).2) (fun c => (sp' c).1) hj hj' hf'
    refine hU n s s' b b' lam mu τ τ' hτ hτ' ⟨hb, hl, hc⟩ ⟨hb', hl', hc'⟩
      (fun c c' h => hj (labO_eq_of_cuspIso O (hl c).1 (hl c').1 h)) ⟨π, fun c => ?_⟩
    haveI := fiber_nonempty hb c
    haveI := fiber_nonempty hb' (π c)
    exact cuspIso_of_labO_eq O (hl c).1 (hl c).2 (hl' _).1 (hl' _).2 (hπ c).symm

theorem main : ReciprocityTheory.Ty.Fin.St.MirrorsOf := by
  intro K _ _ _ C O hE hU hS
  exact ⟨hcLabelO hE hU O, fun hP => ⟨labelSurjO O hP, sqfreeO hS O hP⟩⟩

end GlobalTheory.CompanionTheory.TyFin.Mirrors
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEvCongr
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC
open CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.CompanionTheory.EdgeRep

theorem mul_ev_congr {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k s t : ℤ}
    (h : n + m = k) (hst : s + t = k) (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m) :
    μ.mul X s t k hst (ev α 0 s hs X (𝟙 X)) (ev β 0 t ht X (𝟙 X)) =
      μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  obtain rfl : s = n := by simpa using hs.symm
  obtain rfl : t = m := by simpa using ht.symm
  rfl

theorem aw_value {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k : ℤ}
    (h : n + m = k) (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m)
    (γ : Cochain ((chains R).obj (sch.obj X)) K k) (hγ : μ.IsAW h α β γ) :
    ev γ 0 k (by simp) X (𝟙 X) = μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  have h0 := hγ 0 k (by simp) X (𝟙 X)
  rw [Fin.sum_univ_one] at h0
  rw [h0]
  have hu : (m * ((0 : Fin 1) : ℕ)).negOnePow = 1 := by simp
  rw [hu, one_smul]
  exact mul_ev_congr μ h _ _ _ α β

theorem repCup : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepCup := by
  intro _ _ _ _ _ R _ I J K μ X n m k h x y a b hx hy
  obtain ⟨α, rfl, rfl⟩ := hx
  obtain ⟨β, rfl, rfl⟩ := hy
  obtain ⟨γ, hγ⟩ := μ.aw_exists (sch.obj X) h α β
  exact ⟨γ, (μ.cup_spec (sch.obj X) h α β γ hγ).symm, aw_value μ h α.1 β.1 γ.1 hγ⟩

end GlobalTheory.CompanionTheory.EdgeRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCZsmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMapPull

universe w w' w₁ w₁' u v u' v'

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w'} R} {F' : C' ⥤ ModuleCat.{w₁'} R'}
  {T : Res.{w} F} {T' : Res.{w₁} F'} {m : Mor F F' σ}

theorem d_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    d (T'.K s) k (n.pullC s k x) = n.pullC s (k + 1) (d (T.K s) k x) := by
  funext t
  change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((T'.K s).map (GlobalTheory.CatH.toLast i t)).hom
      (n.τ s _ (x (GlobalTheory.CatH.face i t ⋙ m.G))) =
    n.τ s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((T.K s).map (m.G.map (GlobalTheory.CatH.toLast i t))).hom (x (GlobalTheory.CatH.face i t ⋙ m.G)))
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, n.nat]

theorem dvC_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    T'.dvC s k (n.pullC s k x) = n.pullC (s + 1) k (T.dvC s k x) :=
  funext fun t => (n.dv s _ (x (t ⋙ m.G))).symm

theorem ιC_pullC (n : ResMor T T' m) (k : ℕ) (z : Cn F k) :
    T'.ιC k (m.pullC k z) = n.pullC 0 k (T.ιC k z) :=
  funext fun t => (n.ι _ (z (t ⋙ m.G))).symm

theorem pullC_zsmul (n : ResMor T T' m) (s k : ℕ) (c : ℤ) (x : Cn (T.K s) k) :
    n.pullC s k (c • x) = c • n.pullC s k x :=
  funext fun t => map_zsmul (n.τ s _) c (x (t ⋙ m.G))

theorem st_pullC (n : ResMor T T' m) {j : ℕ} (z : Cn F j) :
    ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T'.St (m.pullC j z) s k (n.pullC s k x)
  | 0, k, x, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, ιC_pullC n j z⟩
  | s + 1, k, x, h => by
    obtain ⟨a, rfl, ha⟩ := h
    refine ⟨n.pullC s k a, dvC_pullC n s k a, ?_⟩
    have := st_pullC n z s (k + 1) _ ha
    rwa [pullC_zsmul, ← d_pullC] at this

end GlobalTheory.CompanionTheory.EdgeMapPull

open GlobalTheory.CompanionTheory.EdgeMapPull in

theorem GlobalTheory.CompanionTheory.EdgeMapPull.edgeMap : CrystallineSemistableComparison.E.EdgeMap := by
  intro R R' _ _ σ C C' _ _ F F' T T' m n j x h hE
  obtain ⟨z, hz, hS, rfl⟩ := hE
  exact ⟨m.pullC j z, by rw [m.d_pullC, hz, map_zero], st_pullC n z j 0 x hS, rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedResMor
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EdgeRed

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom x) h).symm

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C']

def redResMor (hS : KapSpec) (hK : KapRed) (hR : InRed) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q)
    (P : Probe C Q) (P' : Probe C' q) (m : Mor P.L P'.L (RingHom.id ℤ))
    (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (hτ : ∀ c (f : LocallyConstant (P.U (m.G.obj c)) (ZMod Q)),
      m.τ c f = lcRes q (g c) (f.map (ZMod.castHom h (ZMod q))))
    (hζ : ∀ c, (P'.ζ c).1 = (primRes (g c) (P.ζ _)).1 ^ (Q / q)) (i : ℤ) :
    ResMor (P.res i) (P'.res i) m where
  τ s c :=
    { toFun := fun x => Sec.res (g c) ((redMap Q q i).app (P.U (m.G.obj c)) (s : ℤ) x)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  nat s {c c'} φ x := by
    change Sec.res (g c') ((redMap Q q i).app _ (s : ℤ) (Sec.res (P.S.map (m.G.map φ)).unop x)) =
      Sec.res (P'.S.map φ).unop (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).nat, res_res, res_res, hg]
  ι c x := by
    change Sec.res (g c) ((redMap Q q i).app _ 0 (Sec.map (resι _ (tw Q i)) (kap i (P.ζ (m.G.obj c)) x))) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [(redMap Q q i).nat, res_map, (hS Q i _ (P.ζ (m.G.obj c)) x).2.2 _ (g c),
      hK hR Q q h i _ (primRes (g c) (P.ζ (m.G.obj c))) (P'.ζ c) (hζ c), hτ]
    rfl
  dv s c x := by
    change Sec.res (g c) ((redMap Q q i).app _ ((s + 1 : ℕ) : ℤ) (Sec.map ((GlobalTheory.EtC.res _ (tw Q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x)) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).comm, res_map]

theorem etRed : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.KapSpec →
    CrystallineSemistableComparison.E.KapRed → CrystallineSemistableComparison.E.EtRed := by
  intro hSpec hEdge hRep hOpR hS hK hGen hR hOp Q q _ _ h C C' _ _ P P' X Y Y' m g hg hτ hy hζ i j x
  obtain ⟨a, ha⟩ := (hRep _ _ X (j : ℤ)).1 x
  have hE := (hSpec hGen Q C P X Y i j x).1 a ha
  have hE' := hEdge ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m
    (redResMor hS hK hR h P P' m g hg hτ hζ i) j _ _ hE
  have hr : Rep (red Q q _ (j : ℤ) i x) ((redMap Q q i).app X (j : ℤ) a) :=
    hOpR hOp _ _ _ _ (redMap Q q i) X (j : ℤ) x a ha
  refine (hSpec hGen q C' P' X Y' i j (red Q q _ (j : ℤ) i x)).2 _ ⟨_, hr, ?_⟩
  convert hE' using 1
  funext t
  change Sec.res (Y'.y _) ((redMap Q q i).app X (j : ℤ) a) =
    Sec.res (g _) ((redMap Q q i).app _ (j : ℤ) (Sec.res (Y.y _) a))
  rw [← (redMap Q q i).nat, res_res, hy]

end GlobalTheory.CompanionTheory.EdgeRed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepBasic
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtEdge

theorem repBasic : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic := by
  intro hExt hNat hIn
  unfold CrystallineSemistableComparison.E.InSch at hIn
  unfold CrystallineSemistableComparison.E.RepBasic
  intro R _ I X n
  unfold CrystallineSemistableComparison.E.Rep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩ m
    by_cases hm : n + 1 = m
    · exact ((hIn R X I (n - 1) n m (by omega) hm).2 α).1
    · rw [HomologicalComplex.shape I n m (by simpa using hm)]
      simp [GlobalTheory.EtC.Sec.map]
  · rintro x y a b ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    have hs := (hExt R (sch.obj X) I n α β).2 0 n (by simp) X (𝟙 X : X ⟶ X)
    exact ⟨⟨α + β, rfl, hs.1⟩, ⟨α - β, rfl, hs.2.1⟩⟩
  · rintro a ⟨α, h0, rfl⟩ k hk
    exact ((hIn R X I k n (n + 1) hk rfl).2 α).2.1 h0
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨GlobalTheory.EtC.zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h2 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) Y).2 (sch.obj Y) (sch.map f)
      (𝟙 Y : Y ⟶ Y)
    have h1 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) X).1 Y f (𝟙 X : X ⟶ X)
    have e : (Sx.map (sch.map f) (𝟙 Y : Y ⟶ Y) : Sx (sch.obj X) 0 Y) = Sx.res f (𝟙 X : X ⟶ X) := by
      show 𝟙 Y ≫ f = f ≫ 𝟙 X
      simp
    refine h2.trans ?_
    rw [e]
    exact h1

end GlobalTheory.CompanionTheory.EtEdge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepConcOfInputs
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem repConc_of_inputs : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc := by
  intro hEv hSch hRep R _ I X n a
  have hS := hSch R X I (n - 1) n (n + 1) (by ring) rfl
  have hR := hRep R I X n
  have hconc : Sec.map (I.d n (n + 1)) a = 0 →
      ∃ α : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.IsConc α.1 a := by
    intro ha
    obtain ⟨α, h0, h1⟩ := hS.1 a ha
    refine ⟨α, ?_⟩
    unfold CrystallineSemistableComparison.E.IsConc
    exact ⟨h0, h1⟩
  have huniq : ∀ x y : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.Rep x a → CrystallineSemistableComparison.E.Rep y a → x = y := by
    intro x y hx hy
    have hxy : CrystallineSemistableComparison.E.Rep (x - y) (a - a) := (hR.2.2.1 x y a a hx hy).2
    rw [sub_self] at hxy
    obtain ⟨γ, hγ, hγa⟩ := hxy
    have h00 : CrystallineSemistableComparison.E.Rep (0 : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n) 0 := by
      have h := (hR.2.2.1 x x a a hx hx).2
      rwa [sub_self, sub_self] at h
    obtain ⟨b, hb⟩ := hR.2.2.2.1 0 h00 (n - 1) (by ring)
    have hγ0 : CochainComplex.HomComplex.CohomologyClass.mk γ = 0 := ((hS.2 γ).2).2 ⟨b, by rw [hb, hγa]⟩
    rw [← sub_eq_zero, ← hγ, hγ0]
  refine ⟨hconc, fun x hx => ?_, huniq⟩
  have hx' := hx
  obtain ⟨β, hβ, hβa⟩ := hx'
  have ha : Sec.map (I.d n (n + 1)) a = 0 := by
    have h := (hS.2 β).1
    rwa [hβa] at h
  obtain ⟨α, hα⟩ := hconc ha
  have hα' := hα
  unfold CrystallineSemistableComparison.E.IsConc at hα'
  obtain ⟨hα1, -⟩ := hα'
  have hRα : CrystallineSemistableComparison.E.Rep (CochainComplex.HomComplex.CohomologyClass.mk α) a := by
    unfold CrystallineSemistableComparison.E.Rep
    refine ⟨α, rfl, ?_⟩
    rw [hα1 X (𝟙 X)]
    simp [GlobalTheory.EtC.Sec.res]
  exact ⟨α, hα, huniq _ _ hRα hx⟩

end GlobalTheory.CompanionTheory.EdgeMap
end

