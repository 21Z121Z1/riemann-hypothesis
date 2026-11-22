import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0101
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0086
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0099
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0027

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApprox
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem approxC : ProdE.ApproxC M δ u u' F0 what₂ := by
  intro γ w F' L U hE
  obtain ⟨S, hSAC, hSint⟩ := good_places M δ u u' w hE.1 L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
  exact ⟨S, hSAC, fun p => finIdx_at M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1,
    fun h => approx_core M δ u u' w hE.1 L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1 S hSint h⟩

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SecondValueMul
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

theorem first_value_mul (x y : UP p) : (((x * y : UP p) : GG p).1 : GLp p).val =
    (((x : GG p).1 : GLp p).val) * (((y : GG p).1 : GLp p).val) := rfl

theorem second_value_mul (x y : UP p) : ((((x * y : UP p) : GG p).2.unop : GLp p)).val =
    ((((y : GG p).2.unop : GLp p)).val) * ((((x : GG p).2.unop : GLp p)).val) := rfl

def fC : Quotient (CountAb.cellRel (a.mat) πa.ker (KU M p) g) → Quotient (Formalism.L2.SG.Pf.Coef.cellSetoid (M p) a) :=
  Quotient.lift (fun x => Quotient.mk _ (pairOfU a πa hker x.1 (MonoidHom.mem_ker.1 x.2.1))) (by
    intro x y hxy
    apply Quotient.sound
    have hk : (y : UP p) * (x : UP p)⁻¹ ∈ KU M p := hxy.1
    have hy : (y : UP p) = ((y : UP p) * (x : UP p)⁻¹) * (x : UP p) := by group
    refine ⟨⟨((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).1 : GLp p).val, hk.1, ?_⟩,
      ⟨((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p).val, hk.2, ?_⟩⟩
    · show (((y : UP p) : GG p).1 : GLp p).val = _
      conv_lhs => rw [hy]
      rw [first_value_mul]
      rfl
    · show ((((y : UP p) : GG p).2.unop : GLp p)).val = _
      conv_lhs => rw [hy]
      rw [second_value_mul]
      rfl)

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupActB
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupActB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem cong_at_pair {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hc : IsFixedConv Λ (Lat.gS D) F) (hc' : IsFixedConv Λ (Lat.gS D) F')
    (hz' : F'.fl.z ∈ Λ) (hadm : ∀ b, ModG (VS D) Λ (Lat.gS D) (F'.fl.fvec b - F.fl.fvec b))
    (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hν : ∀ v ∈ Λ, ν v ∈ Λ) (hm : ∀ v ∈ Λ, m v ∈ Λ)
    (F'' : LFlag (VS D) D.R.rS T') (hadm'' : ∀ b, ModG (VS D) Λ (Lat.gS D) (F''.fl.fvec b - F.fl.fvec b))
    (hf'' : ∀ b, F''.fl.fvec b = ν⁻¹ (m (F'.fl.fvec b)))
    (uu uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu) (huu' : IsUpUni uu')
    (hfr : ∀ b, ν (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (hfr' : ∀ b, m (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (j i : Fin (D.R.rS + 1)) (hji : j < i) :
    ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E,
      (t : D.host.E) * (uu j i - uu' j i) = ((Lat.gS D : ℕ) : D.host.E) * o := by
  have hP := P.isPrime
  set g : 𝓞 D.host.E := ((Lat.gS D : ℕ) : 𝓞 D.host.E) with hg
  set M := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {g} • Λ) with hM
  have hg0 : ((Lat.gS D : ℕ) : D.host.E) ≠ 0 := by
    have h2 : (Lat.gS D : ℕ) ≠ 0 := by
      unfold Lat.gS
      exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    exact_mod_cast h2

  have hgs : ∀ x : (VS D).V, x ∈ Ideal.span {g} • Λ ↔ ∃ l ∈ Λ, g • l = x := by
    intro x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  have hd : ∀ c, F'.fl.fvec c - F.fl.fvec c ∈ M := fun c => hadm c P hgP
  have hsd : m (F'.fl.fvec i) - ν (F.fl.fvec i) ∈ M := by
    have e : m (F'.fl.fvec i) - ν (F.fl.fvec i) = ν (F''.fl.fvec i - F.fl.fvec i) := by
      rw [map_sub, hf'' i]
      simp [LinearEquiv.coe_inv]
    rw [e]
    obtain ⟨t, ht, htd⟩ := (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).1 (hadm'' i P hgP)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).2 ⟨t, ht, ?_⟩
    rw [← Formalism.L2.SG.Pf.ZsVolLat.smul_O, ← hlg, Formalism.L2.SG.Pf.ZsVolLat.smul_O]
    exact (hgs _).2 ⟨ν l, hν l hl, rfl⟩
  have hud : ∀ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) ∈ M := by
    intro c
    obtain ⟨t1, ht1, o, ho⟩ := Formalism.L2.SG.Pf.ZsVolLat.int_at F' Λ hc' hz' m hm uu' huu' hfr' P hgP c i
    obtain ⟨t2, ht2, htd⟩ := (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).1 (hd c)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).2 ⟨t1 * t2, fun h => (hP.mem_or_mem h).elim ht1 ht2, ?_⟩
    have e : (t1 * t2) • (uu' c i • (F'.fl.fvec c - F.fl.fvec c)) = o • (t2 • (F'.fl.fvec c - F.fl.fvec c)) := by
      rw [← algebraMap_smul D.host.E (t1 * t2), ← algebraMap_smul D.host.E o, ← algebraMap_smul D.host.E t2, smul_smul,
        smul_smul]
      have ho' : algebraMap (𝓞 D.host.E) D.host.E t1 * uu' c i = algebraMap (𝓞 D.host.E) D.host.E o := ho
      rw [map_mul, mul_right_comm, ho']
    rw [e, ← hlg]
    exact (hgs _).2 ⟨o • l, Λ.smul_mem o hl, smul_comm g o l⟩

  set y : Fin D.R.rS → D.host.E := fun a => uu' (Fin.castSucc a) i - uu (Fin.castSucc a) i with hy
  have hlast : uu' (Fin.last _) i - uu (Fin.last _) i = 0 := by
    by_cases h : i = Fin.last _
    · subst h
      rw [(huu' _ _).2 rfl, (huu _ _).2 rfl, sub_self]
    · have hlt : i < Fin.last _ := lt_of_le_of_ne (Fin.le_last i) h
      rw [(huu' _ _).1 hlt, (huu _ _).1 hlt, sub_self]
  have hw : ∑ a, y a • F.fl.e a = (m (F'.fl.fvec i) - ν (F.fl.fvec i)) - ∑ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) := by
    rw [hfr i, hfr' i]
    simp only [smul_sub, Finset.sum_sub_distrib]
    have h2 : ∑ c, (uu' c i - uu c i) • F.fl.fvec c = ∑ a, y a • F.fl.e a := by
      rw [Formalism.L2.SG.Pf.ZsVolLat.sum_fvec]
      simp only [hy, hlast, zero_smul, add_zero]
    rw [← h2]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  have hwM : ∑ a, y a • F.fl.e a ∈ M := by
    rw [hw]
    exact M.sub_mem hsd (M.sum_mem fun c _ => hud c)
  obtain ⟨t, ht, htw⟩ := (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).1 hwM
  obtain ⟨l, hl, hlg⟩ := (hgs _).1 htw

  have hl_eq : l = ∑ a, (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a)) • F.fl.e a := by
    have h1 : ((Lat.gS D : ℕ) : D.host.E) • l = t • ∑ a, y a • F.fl.e a := by
      rw [← hlg, ← algebraMap_smul D.host.E g]
      rfl
    have h2 := congrArg (fun v => ((Lat.gS D : ℕ) : D.host.E)⁻¹ • v) h1
    simp only [smul_smul, inv_mul_cancel₀ hg0, one_smul] at h2
    rw [h2, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t, smul_smul, smul_smul, mul_assoc]
  have hlX : l ∈ XLam Λ F := by
    refine Submodule.mem_inf.2 ⟨hl, ?_⟩
    show l ∈ F.fl.X
    rw [hl_eq]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hloc : l ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
    rw [← Formalism.L2.SG.Pf.ZsVolLat.conv_at F Λ hc P hgP]
    exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hlX⟩
  obtain ⟨t', ht', ht'l⟩ := (Formalism.L2.SG.Pf.ZsVolLat.mem_locP P.asIdeal _ _).1 hloc
  have hv2 : t' • l = ∑ a, ((t' : D.host.E) * (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a))) • F.fl.e a := by
    rw [hl_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t', smul_smul]
  have hjr : (j : ℕ) < D.R.rS := lt_of_lt_of_le hji (Nat.lt_succ_iff.1 i.2)
  obtain ⟨o, ho⟩ := Formalism.L2.SG.Pf.ZsVolLat.coef_spanO F.fl ht'l _ hv2 ⟨j, hjr⟩
  refine ⟨t' * t, fun h => (hP.mem_or_mem h).elim ht' ht, -o, ?_⟩
  have hyj : y ⟨j, hjr⟩ = uu' j i - uu j i := rfl
  rw [hyj] at ho
  have hgi : ((Lat.gS D : ℕ) : D.host.E) * ((Lat.gS D : ℕ) : D.host.E)⁻¹ = 1 := mul_inv_cancel₀ hg0
  push_cast
  linear_combination ((Lat.gS D : ℕ) : D.host.E) * ho + ((t' : D.host.E) * (t : D.host.E) * (uu' j i - uu j i)) * hgi

theorem cong_glob_pair {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hc : IsFixedConv Λ (Lat.gS D) F) (hc' : IsFixedConv Λ (Lat.gS D) F')
    (hX : XLam Λ F = XS D F.fl) (hX' : XLam Λ F' = XS D F'.fl) (hz : F.fl.z ∈ Λ) (hz' : F'.fl.z ∈ Λ)
    (hadm : ∀ b, ModG (VS D) Λ (Lat.gS D) (F'.fl.fvec b - F.fl.fvec b))
    (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hν : ∀ v ∈ Λ, ν v ∈ Λ) (hm : ∀ v ∈ Λ, m v ∈ Λ)
    (F'' : LFlag (VS D) D.R.rS T') (hadm'' : ∀ b, ModG (VS D) Λ (Lat.gS D) (F''.fl.fvec b - F.fl.fvec b))
    (hf'' : ∀ b, F''.fl.fvec b = ν⁻¹ (m (F'.fl.fvec b)))
    (uu uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu) (huu' : IsUpUni uu')
    (hfr : ∀ b, ν (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (hfr' : ∀ b, m (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c)
    (j i : Fin (D.R.rS + 1)) (hji : j < i) :
    uu j i - uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D ((i : ℕ) - (j : ℕ)) := by
  have h1 : uu j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) := Formalism.L2.SG.Pf.ZsVolLat.frame_entry F Λ hX hz ν hν uu huu hfr j i hji
  have h2 : uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) :=
    Formalism.L2.SG.Pf.ZsVolLat.frame_entry F' Λ hX' hz' m hm uu' huu' hfr' j i hji
  have hd : uu j i - uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) :=
    (FractionalIdeal.mem_coe).1 (Submodule.sub_mem _ ((FractionalIdeal.mem_coe).2 h1) ((FractionalIdeal.mem_coe).2 h2))
  refine (FractionalIdeal.mem_coe).1 (Formalism.L2.SG.Pf.ZsVolLat.mem_of_loc _ _ fun P => ?_)
  by_cases hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨t, ht, o, ho⟩ := cong_at_pair F F' Λ hc hc' hz' hadm ν m hν hm F'' hadm'' hf'' uu uu' huu huu' hfr hfr' P hgP j i hji
    refine ⟨t, ht, ?_⟩
    rw [ho]
    exact (FractionalIdeal.mem_coe).2 (Formalism.L2.SG.Pf.ZsVolLat.g_mul_mem (Formalism.L2.SG.Pf.ZsVolLat.o_mem_ddPow _ o))
  · refine ⟨((Lat.gS D : ℕ) : 𝓞 D.host.E), hgP, ?_⟩
    have e : (((Lat.gS D : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Lat.gS D : ℕ) : D.host.E) := by simp
    rw [e]
    exact (FractionalIdeal.mem_coe).2 (Formalism.L2.SG.Pf.ZsVolLat.g_mul_mem hd)

variable (M : ∀ p : LocalSplitGroups.PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : LocalSplitGroups.PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem moveCZ_holds : Formalism.L2.SG.Pf.ZsVolAct.MoveCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH a' b ha hb hst hES
  obtain ⟨hA, -, hR, hP, hE, hN⟩ := hH
  have hΛ : IsRowLat D F0 γ.lam := hR.1 γ.lam γ.mem
  have h' := Formalism.L2.SG.Pf.TupAct.ez_of_normRep hΛ hE hN
  obtain ⟨p', e'⟩ := hN.1
  obtain ⟨ν, hν, m, hm, hνF, hmF, F2, hF2, hr2, hf2⟩ :=
    Formalism.L2.SG.Pf.TupAct.moveCZ hΛ hP.1.ne_zero hP.2.2.1.ne_zero ⟨δ, M, hA⟩ h' ⟨p', e'⟩ ha hb hst hES
  exact ⟨ν, m, F2, ha, hb, hst, hES, hν, hm, hνF, hmF, hF2, hr2, hf2⟩

theorem ontoCZ_holds : Formalism.L2.SG.Pf.ZsVolAct.OntoCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH F'' hF'' hr''
  obtain ⟨hA, -, hR, hP, hE, hN⟩ := hH
  have hΛ : IsRowLat D F0 γ.lam := hR.1 γ.lam γ.mem
  obtain ⟨_, ⟨_, _, hLift, hConv⟩, hXF⟩ := hΛ
  obtain ⟨⟨⟨hLift', _, hFOK⟩, e'⟩, hAdm, _, _, _⟩ := hN
  obtain ⟨p'', e''⟩ := hr''
  obtain ⟨n, hn, m, hm, hfr, -⟩ := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam (hR.1 γ.lam γ.mem)
    ⟨F', ⟨hLift', ‹_›, hFOK⟩⟩ ⟨F'', p''⟩).1 (e'.trans e''.symm)
  have hν : n⁻¹ ∈ NLam γ.lam (lf D F0) := Formalism.L2.SG.Pf.nlamPf_inv hn
  have hf'' : ∀ b, F''.fl.fvec b = (n⁻¹)⁻¹ (m (F'.fl.fvec b)) := fun b => by rw [inv_inv]; exact hfr b
  have hν0 := hν
  have hm0 := hm
  obtain ⟨⟨hisoν, hgν⟩, hf1, hf2⟩ := hν
  obtain ⟨uu, huu, hu⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 n⁻¹ hf1 hf2
  obtain ⟨⟨hisom, hgm⟩, hg1, hg2⟩ := hm
  obtain ⟨uu', huu', hu'⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F'.fl m hg1 hg2
  have hνΛ : ∀ v ∈ γ.lam, n⁻¹ v ∈ γ.lam := fun v hv => by
    rw [← hgν]; exact Submodule.mem_map_of_mem hv
  have hmΛ : ∀ v ∈ γ.lam, m v ∈ γ.lam := fun v hv => by
    rw [← hgm]; exact Submodule.mem_map_of_mem hv
  have hdet : IsUnit uu.conjTranspose.det := by
    rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu)]; exact isUnit_one
  let a' : PairVal.GLR D := Matrix.nonsingInvUnit uu.conjTranspose hdet
  have ha' : (a' : PairVal.MatR D) = uu.conjTranspose := rfl
  have hSS : Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM (K := D.host.E) D.R.rS * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS = 1 :=
    Formalism.L2.SG.Pf.AtPt.sg_sq D.R.rS
  let b : PairVal.MatR D := Formalism.L2.SG.Pf.ZsVolAct.sbs uu'
  have hsbs : Formalism.L2.SG.Pf.ZsVolAct.sbs b = uu' := by
    simp only [b, Formalism.L2.SG.Pf.ZsVolAct.sbs, Matrix.mul_assoc]
    rw [hSS, Matrix.mul_one, ← Matrix.mul_assoc, hSS, Matrix.one_mul]
  have hbU : IsUpUni b := by
    intro i j
    simp only [b, Formalism.L2.SG.Pf.ZsVolAct.sbs, Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM, Matrix.mul_diagonal, Matrix.diagonal_mul]
    refine ⟨fun h => by rw [(huu' i j).1 h, mul_zero, zero_mul], fun h => ?_⟩
    subst h
    rw [(huu' i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp
  have hiso : ∀ x y, (VS D).hT ((n⁻¹) x) ((n⁻¹) y) = (VS D).hT x y := hisoν
  have hZ1 : uu.conjTranspose * ZhatL (lf D F0) F' * uu' = ZhatL (lf D F0) F' := by
    have hZ'' : ZhatL (lf D F0) F'' = ZhatL (lf D F0) F' := hF''.2.2.2.2
    funext a c
    rw [← Formalism.L2.SG.Pf.TupLift.zhat_lift (lf D F0) F' hiso hu hu' a c, ← hZ'']
    show (VS D).hT (F0.fvec a) ((n⁻¹)⁻¹ (m (F'.fl.fvec c))) = (VS D).hT (F0.fvec a) (F''.fl.fvec c)
    rw [hf'' c]
  have hadm : ∀ b, ModG (VS D) γ.lam (Lat.gS D) (F'.fl.fvec b - (lf D F0).fl.fvec b) := fun b => by
    have h := hAdm.2.2 b
    rwa [Formalism.L2.SG.Pf.TupOrb.frameAct_one'] at h
  have hadm'' : ∀ b, ModG (VS D) γ.lam (Lat.gS D) (F''.fl.fvec b - (lf D F0).fl.fvec b) := fun b => by
    have h := hF''.2.1.2.2 b
    rwa [Formalism.L2.SG.Pf.TupOrb.frameAct_one'] at h
  refine ⟨a', b, n⁻¹, m, ?_, hbU, ?_, ?_, hν0, hm0, ?_, ?_, hF'', ⟨p'', e''⟩, hf''⟩
  · rw [ha']; exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu
  · rw [ha', Formalism.L2.SG.Pf.AtPt.zhatOM_eq]
    calc uu.conjTranspose * (ZhatL (lf D F0) F' * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) * b
        = uu.conjTranspose * ZhatL (lf D F0) F' * (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * b) := by
          simp only [Matrix.mul_assoc]
      _ = uu.conjTranspose * ZhatL (lf D F0) F' * uu' * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS := by
          have : Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * b = uu' * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS := by
            simp only [b, Formalism.L2.SG.Pf.ZsVolAct.sbs, ← Matrix.mul_assoc]
            show Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS = _
            rw [hSS, Matrix.one_mul]
            rfl
          rw [this]; simp only [Matrix.mul_assoc]
      _ = ZhatL (lf D F0) F' * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS := by rw [hZ1]
  · intro i j hji
    have hk : ((i : ℕ) - (j : ℕ)) ≤ D.R.rS := by have := i.2; omega
    have h1 := Formalism.L2.SG.Pf.ZsVolLat.frame_entry (lf D F0) γ.lam hXF hLift.1 n⁻¹ hνΛ uu huu hu j i hji
    have h2 := Formalism.L2.SG.Pf.ZsVolLat.frame_entry F' γ.lam hFOK.2 hLift'.1 m hmΛ uu' huu' hu' j i hji
    have h3 := cong_glob_pair (lf D F0) F' γ.lam hConv hFOK.1 hXF hFOK.2 hLift.1 hLift'.1 hadm n⁻¹ m hνΛ hmΛ F''
      hadm'' hf'' uu uu' huu huu' hu hu' j i hji
    rw [ha']
    simp only [b, Formalism.L2.SG.Pf.ZsVolAct.sbs]
    rw [Matrix.conjTranspose_apply, Formalism.L2.SG.Pf.ZsVolLat.bt_sgn, Formalism.L2.SG.Pf.ZsVolLat.star_conjF]
    refine ⟨Formalism.L2.SG.Pf.ZsVolLat.conj_ddPow δ M hA hk h1, h2, ?_⟩
    rw [← map_sub]
    exact Formalism.L2.SG.Pf.ZsVolLat.conj_qdPow δ M hA hk h3
  · intro c
    rw [ha', Matrix.conjTranspose_conjTranspose]
    exact hu c
  · intro c
    rw [hsbs]
    exact hu' c

end Formalism.L2.SG.Pf.TupActB

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFib
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem act_mul (f : Fin (D.R.rS + 1) → (VS D).V) (s s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A B : MatR D)
    (hs : ∀ b, s (f b) = ∑ c, A c b • f c) (hs' : ∀ b, s' (f b) = ∑ c, B c b • f c) (b : Fin (D.R.rS + 1)) :
    (s * s') (f b) = ∑ c, (A * B) c b • f c := by
  show s (s' (f b)) = _
  rw [hs', map_sum]
  simp only [map_smul, hs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem act_inv' (f : Fin (D.R.rS + 1) → (VS D).V) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A : MatR D)
    (hA : IsUpUni A) (hs : ∀ b, s (f b) = ∑ c, A c b • f c) (b : Fin (D.R.rS + 1)) :
    s⁻¹ (f b) = ∑ c, A⁻¹ c b • f c := by
  apply s.injective
  show s (s.symm (f b)) = _
  rw [LinearEquiv.apply_symm_apply, Formalism.L2.SG.Pf.ZsVolKey.act_inv f s A (Formalism.L2.SG.Pf.ZsVolKey.up_inv_mul hA) hs b]

theorem act_one (f : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f b) = ∑ c, (1 : MatR D) c b • f c := by
  simp [Matrix.one_apply]

theorem nlam_one {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  refine ⟨(Formalism.L2.SG.Pf.isAutLam_iff Λ 1).2 ⟨fun x y => rfl, fun x => Iff.rfl⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · simp
  · simp

variable (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def stabAutG (t : Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D)
    (hL : Formalism.MainNotions.S.IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) : Subgroup (GLR D) where
  carrier := stabAutSet D u u' F0 what₂ t F' L
  one_mem' := by
    refine ⟨1, ⟨nlam_one _ _, nlam_one _ _⟩, 1, act_one _, ?_⟩
    rw [Units.val_one, Matrix.conjTranspose_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one)]
  mul_mem' := by
    rintro x y ⟨s₁, ⟨h1F, h1F'⟩, uu₁, hu₁, hx⟩ ⟨s₂, ⟨h2F, h2F'⟩, uu₂, hu₂, hy⟩
    refine ⟨s₂ * s₁, ⟨Formalism.L2.SG.Pf.nlamPf_mul h2F h1F, Formalism.L2.SG.Pf.nlamPf_mul h2F' h1F'⟩, uu₂ * uu₁,
      act_mul _ _ _ _ _ hu₂ hu₁, ?_⟩
    have hLL : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one)
    rw [Units.val_mul, hx, hy, Matrix.conjTranspose_mul]
    calc L⁻¹ * uu₁.conjTranspose * L * (L⁻¹ * uu₂.conjTranspose * L) =
        L⁻¹ * uu₁.conjTranspose * (L * L⁻¹) * uu₂.conjTranspose * L := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hLL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨s, ⟨hF, hF'⟩, uu, hu, hx⟩

    obtain ⟨⟨⟨hiso, _⟩, hf1, hf2⟩, _⟩ := And.intro hF hF'
    obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
    have heq : uu = uu0 :=
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 hu hu0
    subst heq
    refine ⟨s⁻¹, ⟨Formalism.L2.SG.Pf.nlamPf_inv hF, Formalism.L2.SG.Pf.nlamPf_inv hF'⟩, uu⁻¹, act_inv' _ _ _ huu0 hu, ?_⟩
    have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
    have hUd : IsUnit uu.conjTranspose.det := by
      rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0)]; exact isUnit_one
    rw [Matrix.coe_units_inv, hx, Matrix.conjTranspose_nonsing_inv]
    refine Matrix.inv_eq_left_inv ?_
    calc L⁻¹ * (uu.conjTranspose)⁻¹ * L * (L⁻¹ * uu.conjTranspose * L) =
        L⁻¹ * ((uu.conjTranspose)⁻¹ * (L * L⁻¹) * uu.conjTranspose) * L := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ hLd, Matrix.mul_one, Matrix.nonsing_inv_mul _ hUd, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ hLd]

theorem mem_stabAut_iff (t : Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D)
    (hL : Formalism.MainNotions.S.IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) (a : GLR D) :
    a ∈ stabAut D u u' F0 what₂ t F' L ↔ a ∈ stabAutSet D u u' F0 what₂ t F' L := by
  have e : stabAut D u u' F0 what₂ t F' L = stabAutG u u' F0 what₂ t F' L hL hT0 :=
    Subgroup.closure_eq (stabAutG u u' F0 what₂ t F' L hL hT0)
  rw [e]
  rfl

end Formalism.L2.SG.Pf.ZsVolFib

end
end

