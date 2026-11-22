import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0387

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.Enlarge
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private noncomputable def listProd {ι : Type} {a b : ℕ} (d : ι → Ex (Fin (a + 1) × Fin (b + 1))) :
    List ι → Ex (Fin (a + 1) × Fin (b + 1))
  | [] => .one
  | i :: l => .mul (d i) (listProd d l)

private theorem list_prod_unitary_test {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (h : ∀ i, U1 (d i)) : ∀ l : List ι, U1 (listProd d l)
  | [] => .one
  | i :: l => .mul (h i) (list_prod_unitary_test h l)

private theorem listProd_ev_zero {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (x : Fin (a + 1) × Fin (b + 1) → ℂ) {i : ι} (h0 : (d i).ev x = 0) :
    ∀ l : List ι, i ∈ l → (listProd d l).ev x = 0
  | [], h => by simp at h
  | j :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [listProd, Ex.ev, h0]
    · simp [listProd, Ex.ev, listProd_ev_zero x h0 l h]

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula

open scoped Classical in
theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.enlarge :
    StUnit → EvaluationAtUnitaryOne → SeparatesUnitaryOne → Places → Enlarge := by
  intro hSt hEv hSep hPl E _ _ _ hunr a b S hS Z T hZ hT hTZ e₁ e₂ I _ u C₁ C₂ hC
  obtain ⟨-, hcp, -, hsec⟩ := hPl E
  have hd : ∀ i, ∃ e, U1 e ∧ ev2 a b (u i) e (C₁ i (u i)) (C₂ i (u i)) = 0 := fun i =>
    hSep E (u i) a b _ _ (hC i).2.1 (hC i).2.2.1 (hC i).2.2.2
  choose d hdU hd0 using hd
  haveI : Fintype I := Fintype.ofFinite I
  have hnsS : ∀ w : Pl E, ¬ IsSplitAt w → w ∈ S := by
    intro w hw
    have hc : cPl w = w := by
      by_contra h
      exact hw ((hcp w).2.2 h)
    rcases (hsec S hS w).1 with h | h
    · exact h
    · rwa [hc] at h
  have hTns : ∀ w ∈ T, IsSplitAt w := fun w hw => (hT w hw).2
  have hZns : ∀ w ∈ Z, IsSplitAt w := fun w hw => (hZ w hw).2
  let L : Pl E → List I := fun w => (Finset.univ.filter fun i => u i = w).toList
  let T' : Finset (Pl E) := T ∪ Finset.univ.image u
  let f₁ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₁ w else listProd d (L w)
  let f₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₂ w else .one
  have hfU : ∀ w, w ∉ T → U1 (f₁ w) := by
    intro w hw
    simp only [f₁, if_neg hw]
    exact list_prod_unitary_test hdU _
  have hf₂ : ∀ w, w ∉ T → f₂ w = .one := fun w hw => by simp only [f₂, if_neg hw]
  have hT'ns : ∀ w ∈ T', w ∉ T → ¬ IsSplitAt w := by
    intro w hw hwT
    rcases Finset.mem_union.1 hw with h | h
    · exact absurd h hwT
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (hC i).1
  have huT : ∀ i, u i ∉ T := fun i h => (hC i).1 (hTns _ h)
  refine ⟨T', f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_cases hwT : w ∈ T
    · exact (hT w hwT).1
    · exact hnsS w (hT'ns w hw hwT)
  · rw [Finset.disjoint_left]
    intro w hw hwZ
    by_cases hwT : w ∈ T
    · exact Finset.disjoint_left.1 hTZ hwT hwZ
    · exact hT'ns w hw hwT (hZns w hwZ)
  · intro w hw hns
    have hwT : w ∉ T := fun h => hns (hTns w h)
    exact hf₂ w hwT
  · intro i
    refine Finset.prod_eq_zero (i := u i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) ?_
    have : ev2 a b (u i) (f₁ (u i)) (C₁ i (u i)) (C₂ i (u i)) = 0 := by
      simp only [f₁, if_neg (huT i)]
      refine listProd_ev_zero _ (hd0 i) _ ?_
      simp [L]
    rw [this, zero_mul]
  · intro B₁ B₂ hB
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.val
    symm
    have hsub : T ⊆ T' := Finset.subset_union_left
    rw [← Finset.prod_subset hsub]
    · refine Finset.prod_congr rfl fun w hw => ?_
      simp only [f₁, f₂, if_pos hw]
    · intro w hw hwT
      rcases Finset.mem_union.1 hw with h | h
      · exact absurd h hwT
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      rw [hf₂ _ hwT, hEv E (u i) a b _ (hfU _ hwT) _ _ (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2]
      simp [ev2, Ex.ev]
  · intro l₁ l₂ φ k
    have hloc : ∀ (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Separable → Q₂.Separable →
        stTw2 a b w Q₁ Q₂ (fam Z T' φ f₁ f₂ k w) = stTw2 a b w Q₁ Q₂ (fam Z T φ e₁ e₂ k w) := by
      intro w Q₁ Q₂ h₁ h₂
      unfold fam
      by_cases hwZ : w ∈ Z
      · simp only [if_pos hwZ]
      simp only [if_neg hwZ]
      by_cases hwT : w ∈ T
      · have hw' : w ∈ T' := Finset.mem_union_left _ hwT
        simp only [if_pos hwT, if_pos hw', f₁, f₂]
      by_cases hw' : w ∈ T'
      · simp only [if_neg hwT, if_pos hw']
        rw [hf₂ w hwT]
        exact hSt E hunr w (hT'ns w hw' hwT) a b _
          (.mul ((hfU w hwT).pow k) ((U1.one).pow k)) Q₁ Q₂ h₁ h₂
      · simp only [if_neg hwT, if_neg hw']
    unfold PositivityTheory.Rg.BcB.G8.geomSt2
    refine finsum_mem_congr rfl fun p hp => ?_
    congr 1
    refine finprod_congr fun w => finprod_congr fun _ => ?_
    exact hloc w _ _ (hp.1.2.2.1.map) (hp.2.1.2.2.1.map)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.GalWeakOfCuspU
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rig PositivityTheory.Rg.BcB.F.Rig.GalX
open GlobalTheory.HeckeGal.Model (absPow absPow_isAbsPow)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

def GalAt (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (N : ℕ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → a ≤ N → ∀ P : CuspSub E a, P.IsCsd → ∀ s : ℝ, (CG.mk (P.twist (absPow E s))).IsRegAlg →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), (P.twist (absPow E s)).IsLocComp w σ →
        ∀ S : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω),
          IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
          (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
            X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-((1 - (a : ℝ)) / 2) : ℝ) : ℂ)))).prod

def GalWeak (N : ℕ) : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∃ (l : ℕ) (_ : Fact l.Prime) (ι : Qbar l ≃+* ℂ), GalAt E (AlgebraicClosure E) ι N

private theorem sideW (hS : StrSat) (hSt : Strings) (hC : CuspCsd) {E : Type} [Field E] [NumberField E] [IsCMField E] (Ω : Type) [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N n : ℕ} (hG : GalAt E Ω ι N) (hN' : n ≤ N) (D : Pre E n)
    (hr : D.Reg) (ht : D.ThetaStable) :
    ∃ (m : ℕ) (R : G E Ω →* GL (Fin m) (Qbar l)), Continuous R ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        (∃ B, D.Sat w B) ∧ ∀ B, D.Sat w B → ∀ (A : ValuationSubring Ω) (g : G E Ω),
          IsPlaceOver (F := E) A w → IsFrob (F := E) A (normV w) g →
          (R (g ^ (-1 : ℤ))).val.charpoly = (B.map fun z : ℂˣ =>
            X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod := by
  classical
  choose a d P ha hd hu hn hemb using hSt E n D hr
  have he : ∀ i, AscEmb (D.V i) (P i) (d i) := fun i => hemb i (P i) (Setoid.refl (α := CuspSub E (a i)) (P i))
  have hcsd : ∀ i, (P i).IsCsd := fun i =>
    hC E n D hr ht i (a i) (d i) (P i) (ha i) (hd i) (hu i) (hn i) (he i)
  have hle : ∀ i, a i ≤ N := fun i => by
    obtain ⟨h, -⟩ := he i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    have h1 : D.N i ≤ n := (Finset.single_le_sum (f := D.N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D.h.le
    have h2 : a i ≤ d i * a i := Nat.le_mul_of_pos_left _ (hd i)
    omega
  let s : (Σ i : Fin D.c, Fin (d i)) → ℝ := fun x => spehExp (d x.1) x.2 + ((a x.1 : ℝ) - n) / 2
  have hreg : ∀ x : (Σ i : Fin D.c, Fin (d i)), (CG.mk ((P x.1).twist (absPow E (s x)))).IsRegAlg :=
    fun x => regTw D hr x.1 (P x.1) (he x.1) x.2
  choose r hrc hrf using fun x : (Σ i : Fin D.c, Fin (d i)) =>
    hG (a x.1) (ha x.1) (hle x.1) (P x.1) (hcsd x.1) (s x) (hreg x)
  let e := Fintype.equivFin (Σ x : (Σ i : Fin D.c, Fin (d i)), Fin (a x.1))
  refine ⟨_, GlobalTheory.BlockSum.blockRep e r, GlobalTheory.BlockSum.continuous_blockRep e r hrc, ?_⟩
  have hev := Filter.eventually_all.2 fun i => hS E (D.N i) (a i) (d i) (D.V i) (P i) (D.σ i) (D.pos i)
    (D.discrete i) (hu i) (hn i) (he i) (D.loc i) (fun k => absPow E (spehExp (d i) k))
    (fun k => absPow_isAbsPow E _)
  filter_upwards [hev, Filter.eventually_all.2 hrf] with w hw hrw hl
  choose b hb hsph hsat using hw
  refine ⟨⟨_, fun i => ∑ k, b i k, fun i => ⟨hsph i, hsat i⟩, rfl⟩, ?_⟩
  rintro _ ⟨b', hb', rfl⟩ A g hA hg
  have hbb : ∀ i, b' i = ∑ k, b i k := fun i => (hb' i).2.unique (hsat i)
  have hN : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hx : ∀ x : (Σ i : Fin D.c, Fin (d i)), (r x (g ^ (-1 : ℤ))).val.charpoly = ((b x.1 x.2).map fun z : ℂˣ =>
      X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod := by
    rintro ⟨i, k⟩
    have h1 := (CG.HasSat.twist_absPow (hb i k) (((a i : ℝ) - n) / 2)).1
    rw [twist_absPow_absPow] at h1
    obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E (a i)
      ((P i).twist (absPow E (s ⟨i, k⟩))) w
    have h2 : GlobalTheory.LFun.HasSatGL w σ.ρ _ :=
      (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.1 ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ (Fin (a i)) σ.V σ.ρ _).2
        (GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp _ h1 hσ))).2
    rw [hrw ⟨i, k⟩ hl σ hσ _ h2 A g hA hg, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun z _ => ?_)
    simp only [Function.comp_apply, Units.val_mul]
    rw [(absPow_isAbsPow E _).2.1 w, mul_assoc, ← Complex.cpow_add _ _ hN]
    refine congrArg (fun u : ℂ => X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ u))) ?_
    push_cast
    ring
  rw [GlobalTheory.BlockSum.charpoly_blockRep, Finset.prod_congr rfl fun x _ => hx x, Fintype.prod_sigma]
  simp only [hbb]
  rw [prod_map_sum]
  exact Finset.prod_congr rfl fun i _ => (prod_map_sum _ _ _).symm

theorem galStep_le {N : ℕ} (hW : GalWeak N) (E : Type) [Field E] [NumberField E] [IsCMField E] (hu : GlobalTheory.BCT.Unr E) (n : ℕ)
    (hn : n ≤ N) (D D' : Pre E n) (hr : D.Reg) (hr' : D'.Reg) (ht : D.ThetaStable) (ht' : D'.ThetaStable)
    (hsplit : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ D'.Sat w B) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ D'.Sat w B := by
  classical
  obtain ⟨l, _, ι, hG⟩ := hW E hu
  obtain ⟨m, R, hR, hev⟩ := sideW strSat strings_holds cuspCsd_holds (AlgebraicClosure E) ι hG hn D hr ht
  obtain ⟨m', R', hR', hev'⟩ := sideW strSat strings_holds cuspCsd_holds (AlgebraicClosure E) ι hG hn D' hr' ht'
  have hl2 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    have h20 : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    refine Filter.eventually_cofinite.2 ?_
    simpa only [not_not] using Formalism.L2.G.finite_setOf_mem_asIdeal (F := E) h20
  have hall := ((hev.and hev').and (hsplit.and hl2))
  obtain hT := Filter.eventually_cofinite.1 hall
  have hRam := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).2
  let f : G E (AlgebraicClosure E) → ℕ → Qbar l := fun g j => (R g⁻¹).val.charpoly.coeff j
  let f' : G E (AlgebraicClosure E) → ℕ → Qbar l := fun g j => (R' g⁻¹).val.charpoly.coeff j
  have hf : Continuous f := continuous_pi fun j =>
    (PositivityTheory.Rg.DzCong.CongruenceClosure.continuous_coeff_charpoly m j).comp (Units.continuous_val.comp (hR.comp continuous_inv))
  have hf' : Continuous f' := continuous_pi fun j =>
    (PositivityTheory.Rg.DzCong.CongruenceClosure.continuous_coeff_charpoly m' j).comp (Units.continuous_val.comp (hR'.comp continuous_inv))
  have hff : f = f' := GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob (hT.union hRam) hf hf'
    (fun v hv hd A hA σ hσ => by
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hv
      obtain ⟨B, hB, hB'⟩ := h3 (PositivityTheory.Rg.DzCong.CongruenceClosure.isSplitAt_of_deg_one v hd h5)
      have c1 := (h1 h4).2 B hB A σ hA hσ
      have c2 := (h2 h4).2 B hB' A σ hA hσ
      rw [_root_.zpow_neg_one] at c1 c2
      funext j
      simp only [f, f', c1, c2])
  filter_upwards [hev, hev', hl2] with w h1 h2 h4
  obtain ⟨B, hB⟩ := (h1 h4).1
  obtain ⟨B', hB'⟩ := (h2 h4).1
  obtain ⟨A, hA⟩ := exists_isPlaceOver (AlgebraicClosure E) w
  obtain ⟨g, hg⟩ := Formalism.MainNotions.LatticeVariant.exists_isFrob A w hA
  have c1 := (h1 h4).2 B hB A g hA hg
  have c2 := (h2 h4).2 B' hB' A g hA hg
  have e : (R (g ^ (-1 : ℤ))).val.charpoly = (R' (g ^ (-1 : ℤ))).val.charpoly := by
    ext j
    have := congrFun (congrFun hff g) j
    simpa [f, f', _root_.zpow_neg_one] using this
  rw [c1, c2] at e
  have hN : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  let ψ : ℂˣ → Qbar l := fun z => ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2))
  have hψ : Function.Injective ψ := fun z z' h => by
    have h' := ι.symm.injective h
    have hc : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2) ≠ 0 :=
      fun h0 => hN ((Complex.cpow_eq_zero_iff _ _).1 h0).1
    exact Units.ext (mul_right_cancel₀ hc h')
  have key : ∀ C : Multiset ℂˣ, (C.map fun z : ℂˣ =>
      X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod =
      ((C.map ψ).map fun u => X - Polynomial.C u).prod := fun C => by
    rw [Multiset.map_map]
    rfl
  have e2 := congrArg Polynomial.roots e
  rw [key, key, Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  have hBB : B = B' := Multiset.map_injective hψ e2
  exact ⟨B, hB, hBB ▸ hB'⟩

theorem galWeak_of_cuspU (hG : UpperTheory.GalN.CuspU) (hL : GlobalTheory.Published.LocalLanglandsGL) (N : ℕ) : GalWeak N := by
  intro E _ _ _ _
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  refine ⟨2, inferInstance, ι, fun a ha _ P hP s hr => ?_⟩
  obtain ⟨r, wt, HT, H⟩ := hG E (AlgebraicClosure E) 2 ι a ha _ _ hr (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s)
  refine ⟨r, H.cont, Filter.Eventually.of_forall fun w hl σ hσ S hS B g hB hg => ?_⟩
  obtain ⟨rc, hrc⟩ := (hL.1 E _ B w hB).exists
  refine GlobalTheory.T.local_langlands_galois_compat E _ 2 ι a r H.cont w hl B hB rc hrc σ S hS _ ((H.aw hl hrc hσ).eq_unr ?_) g hg
  exact (GlobalTheory.WeilDeligne.WD.unr_tw _ _).2 (UpperTheory.GalN.unr_rec_of_hasSat hrc σ S hS)

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.HeckeEigenvaluesUnitaryOneFactor
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem satEig_rev_of_stable {q n : ℕ} {B : Multiset ℂˣ} (hB : B.card = n) (hs : inv B = B)
    (i : Fin (n + 1)) : satEig q n B (i.rev : ℕ) = satEig q n B n * satEig q n B (i : ℕ) := by
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  have h := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := q) hB hi
  have hs' : B.map (·⁻¹) = B := hs
  rw [hs'] at h
  have hr : (i.rev : ℕ) = n - (i : ℕ) := by
    rw [Fin.val_rev]; omega
  rw [hr, ← h, mul_comm]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.hecke_eigenvalues_unitary_one_factor :
    EvaluationAtUnitaryOne := by
  intro E _ _ _ w a b e he B₁ B₂ h₁ h₂ s₁ s₂
  induction he with
  | one => simp [ev2, Ex.ev]
  | step c p =>
    have r₁ := satEig_rev_of_stable (q := qV E w) h₁ s₁ p.1
    have r₂ := satEig_rev_of_stable (q := qV E w) h₂ s₂ p.2
    simp only [ev2, Ex.ev, dEx, Fin.val_last, r₁, r₂]
    ring
  | mul _ _ ih₁ ih₂ =>
    simp only [ev2, Ex.ev] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.MtoLaws
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem rel_comp {r s t : ℂ → ℂ → Prop} (h : ∀ x y z, r x y → s y z → t x z)
    {a b c : Multiset ℂ} (hab : Multiset.Rel r a b) :
    Multiset.Rel s b c → Multiset.Rel t a c := by
  induction hab generalizing c with
  | zero =>
    intro h0
    rw [Multiset.rel_zero_left] at h0
    subst h0
    exact Multiset.Rel.zero
  | cons hxy _ ih =>
    intro hc
    obtain ⟨z, zs, hz, hzs, rfl⟩ := Multiset.rel_cons_left.1 hc
    exact Multiset.Rel.cons (h _ _ _ hxy hz) (ih hzs)

private theorem exists_sep (S : Finset (ℂ × ℂ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ S, p.1 ≠ p.2 → ε < ‖p.1 - p.2‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert p S _ ih =>
    obtain ⟨ε, h0, hε⟩ := ih
    by_cases hp : p.1 = p.2
    · refine ⟨ε, h0, fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact absurd hp hne
      · exact hε q hq hne
    · have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
      refine ⟨min ε (‖p.1 - p.2‖ / 2), lt_min h0 (half_pos hpos), fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact (min_le_right _ _).trans_lt (half_lt_self hpos)
      · exact (min_le_left _ _).trans_lt (hε q hq hne)

private theorem eq_of_rel {a b : Multiset ℂ}
    (h : ∀ ε : ℝ, 0 < ε → Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) a b) : a = b := by
  classical
  obtain ⟨ε, h0, hε⟩ := exists_sep (a.toFinset ×ˢ b.toFinset)
  refine Multiset.rel_eq.1 ((h ε h0).mono fun x hx y hy hxy => ?_)
  by_contra hne
  exact absurd hxy (not_le.2 (hε (x, y) (by simp [hx, hy]) hne))

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.mtoLaws :
    MToLaws := by
  intro E _ _ _
  refine ⟨fun m x y hx hy => ?_, fun m x z z₀ hx hz τ ε hε => ?_,
    fun m m' x x' hx hx' τ ε hε => ?_⟩
  · funext τ
    refine eq_of_rel fun ε hε => ?_
    obtain ⟨k, h1, h2⟩ := ((hx τ (ε / 2) (half_pos hε)).and (hy τ (ε / 2) (half_pos hε))).exists
    refine rel_comp (fun p q w (hpq : ‖q - p‖ ≤ ε / 2) (hqw : ‖q - w‖ ≤ ε / 2) => ?_)
      (Multiset.rel_flip.2 h1) h2
    calc ‖p - w‖ = ‖(q - w) - (q - p)‖ := by congr 1; ring
      _ ≤ ‖q - w‖ + ‖q - p‖ := norm_sub_le _ _
      _ ≤ ε := by linarith
  · have hz' : ∀ᶠ k in atTop, ‖z k - z₀‖ ≤ ε / 2 :=
      (Metric.tendsto_nhds.1 hz (ε / 2) (half_pos hε)).mono fun k hk => by
        rw [dist_eq_norm] at hk
        exact hk.le
    filter_upwards [hx τ (ε / 2) (half_pos hε), hz'] with k h1 h2
    refine Multiset.rel_map.2 (h1.mono fun p _ q _ hpq => ?_)
    calc ‖(p + z k) - (q + z₀)‖ = ‖(p - q) + (z k - z₀)‖ := by congr 1; ring
      _ ≤ ‖p - q‖ + ‖z k - z₀‖ := norm_add_le _ _
      _ ≤ ε := by linarith
  · filter_upwards [hx τ ε hε, hx' τ ε hε] with k h1 h2
    exact h1.add h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.MuInf
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.muInf :
    MuInf := by
  intro E _ _ _ μ e hμ
  refine ⟨fun w hw => ?_, fun N k P v => ⟨?_, ?_⟩⟩
  · simpa using UpperTheory.HeckeLevelFrameExistence.muVal E μ e hμ w hw 1
  · rw [((ParLaws.hasInfChar_infChar P v.embedding).twist (μ ^ k)).infChar_eq]
    refine Multiset.map_congr rfl fun z _ => ?_
    rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.MuProps.expo_emb hμ]
    ring
  · rw [((ParLaws.hasInfChar_infChar P (ComplexEmbedding.conjugate v.embedding)).twist (μ ^ k)).infChar_eq]
    refine Multiset.map_congr rfl fun z _ => ?_
    rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.MuProps.expo_conj hμ]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.MwAt
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.mwAt :
    MWAt := by
  intro E _ _ _ n l v
  have hne : ComplexEmbedding.conjugate v.embedding ≠ v.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (NumberField.IsTotallyComplex.isComplex v))
      (ComplexEmbedding.isReal_iff.2 h)
  have hmk : InfinitePlace.mk (ComplexEmbedding.conjugate v.embedding) = v := by
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  constructor
  · unfold mW PositivityTheory.Rg.BcB.CG.mOf infOfWeight PositivityTheory.RgBcC.infOf
    simp only [InfinitePlace.mk_embedding, decide_true, if_true, one_mul]
    congr 1
    funext k
    rw [add_sub_assoc]
  · unfold mW PositivityTheory.Rg.BcB.CG.mOf infOfWeight PositivityTheory.RgBcC.infOf
    simp only [hmk, hne, decide_false, Multiset.map_map]
    congr 1
    funext k
    simp only [Function.comp, Bool.false_eq_true, if_false]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.RegOf
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.regOf :
    MWAt → DualWt → RegOf := by
  intro mw dw E _ _ _ n l D hD τ
  have hτ := hD τ
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · refine ⟨l (InfinitePlace.mk τ), ?_⟩
    have h1 := (mw E n l (InfinitePlace.mk τ)).1
    rw [h] at h1
    rw [hτ, h1]
  · obtain ⟨lam, hlam⟩ := dw n (l (InfinitePlace.mk τ))
    refine ⟨lam, ?_⟩
    have hc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h]
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
    have h2 := (mw E n l (InfinitePlace.mk τ)).2
    rw [hc] at h2
    rw [hτ, h2, hlam]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.UnStable
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem inv_map_sign (B : Multiset ℂˣ) (k : ℕ) (h : inv B = B) :
    inv (B.map (· * (-1 : ℂˣ) ^ k)) = B.map (· * (-1 : ℂˣ) ^ k) := by
  have hk : ((-1 : ℂˣ) ^ k)⁻¹ = (-1 : ℂˣ) ^ k := by
    rw [← inv_pow, inv_neg_one]
  conv_rhs => rw [← h]
  simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply, mul_inv, hk]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.unStable :
    UnStable := by
  intro E _ _ _ μ a b w B₁ B₂ hμ h₁ h₂
  have hadd : ∀ X Y : Multiset ℂˣ, inv (X + Y) = inv X + inv Y := fun X Y => Multiset.map_add _ _ _
  simp only [un, hμ]
  rw [hadd, inv_map_sign B₁ b h₁, inv_map_sign B₂ a h₂]
end

