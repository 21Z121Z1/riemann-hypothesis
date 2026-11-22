import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.InfVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.DcMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.LocEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AwayCongr
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem thinOut {α β : Type} [DecidableEq α] (f : α → β) (S T : Finset α) (hinj : Set.InjOn f (S : Set α)) :
    ∃ T' : Finset α, S ⊆ T' ∧ Set.InjOn f (T' : Set α) ∧ (∀ t ∈ T', t ∉ S → ∀ s ∈ S, f s ≠ f t) ∧
      ∀ t ∈ T, ∃ t' ∈ T', f t' = f t := by
  induction T using Finset.induction_on with
  | empty => exact ⟨S, subset_rfl, hinj, fun t h h' => absurd h h', by simp⟩
  | insert a T₀ _ ih =>
    obtain ⟨T', h1, h2, h3, h4⟩ := ih
    by_cases h : ∃ t' ∈ T', f t' = f a
    · refine ⟨T', h1, h2, h3, fun t ht => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact h
      · exact h4 t ht
    · push_neg at h
      refine ⟨insert a T', h1.trans (Finset.subset_insert _ _), ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h₁ | h₁ <;>
          rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with h₂ | h₂
        · rw [h₁, h₂]
        · subst h₁
          exact absurd hxy.symm (h y h₂)
        · subst h₂
          exact absurd hxy (h x h₁)
        · exact h2 h₁ h₂ hxy
      · intro t ht htS s hs
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact h s (h1 hs)
        · exact h3 t ht htS s hs
      · intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact ⟨_, Finset.mem_insert_self _ _, rfl⟩
        · obtain ⟨t', a', b⟩ := h4 t ht
          exact ⟨t', Finset.mem_insert_of_mem a', b⟩

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem away_congr {n : ℕ} {w w' : Plc L} (h : w.under (𝓞 (Lp L)) = w'.under (𝓞 (Lp L))) :
    away n w = away n w' := by
  simp only [away, h]

private theorem cLoc_away {n : ℕ} {w : Plc L} {y : UA L n} (hy : y ∈ away n w) : cLoc w y = 1 :=
  Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy w) rfl

private noncomputable def AT (S : Finset (Plc L)) (W : ∀ w : Plc L, Sig.Lev (Kw w)) (T : Finset (Plc L)) : Subgroup (UA L 2) :=
  lev (Kall L 2) S W ⊓ ⨅ w ∈ T, away 2 w

private theorem step [DecidableEq (Plc L)] {V : Type} [AddCommGroup V] [Module ℂ V] (S T₀ : Finset (Plc L))
    (W : ∀ w : Plc L, Sig.Lev (Kw w)) (w : Plc L)
    (hS : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (hT : ∀ t ∈ T₀, t.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (R : Representation ℂ (InfinitePlace L → GL (Fin 2) ℂ) V) (φ φ' : UA L 2 → V)
    (hspan : InSpan w φ φ') (hAF : IsAF R (AT S W (insert w T₀)) φ)
    (hinv : ∀ x ∈ locU 2 w, x ∈ Kall L 2 → (w ∈ S → cLoc w x ∈ (W w).J 2) → ∀ g, φ' (g * x) = φ' g) :
    IsAF R (AT S W T₀) φ' := by
  have h1 : AT S W (insert w T₀) ≤ away 2 w :=
    inf_le_right.trans (iInf₂_le w (Finset.mem_insert_self _ _))
  have h2 := (spanKeep L 2 V w φ φ' hspan).2.1 R _ h1 hAF
  refine ⟨h2.left, h2.inf, ?_⟩
  intro u hu g
  obtain ⟨x, hx, y, hy, rfl⟩ := (factor L 2 w).2.1 u
  obtain ⟨hlev, hTa⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hK, hJ⟩ := Subgroup.mem_inf.1 hlev
  have hxy := ((factor L 2 w).2.2.2.2.2 x hx y hy).1 hK
  have hJ' : ∀ v ∈ S, cLoc v (x * y) ∈ (W v).J 2 := fun v hv =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hJ v) hv
  have hyw : cLoc w y = 1 := cLoc_away hy
  have hyA : y ∈ AT S W (insert w T₀) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxy.2, ?_⟩, ?_⟩
    · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
      show cLoc v y ∈ (W v).J 2
      by_cases hvw : v = w
      · subst hvw
        rw [hyw]
        exact one_mem _
      · have hxv : cLoc v x = 1 :=
          cLoc_away ((factor L 2 v).2.2.1 w (hS v hv hvw).symm hx)
        have := hJ' v hv
        rwa [map_mul, hxv, one_mul] at this
    · refine Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => ?_
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hy
      · have hxt : x ∈ away 2 t := (factor L 2 t).2.2.1 w (hT t ht).symm hx
        have hxyt : x * y ∈ away 2 t := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hTa t) ht
        exact (Subgroup.mul_mem_cancel_left _ hxt).1 hxyt
  rw [← mul_assoc, h2.level y hyA, hinv x hx hxy.1 ?_]
  intro hwS
  have := hJ' w hwS
  rwa [map_mul, hyw, mul_one] at this

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CompOfEig
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.compOfEig :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ w, IsSplitAt w →
                 ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π → (∀ x ∈ locU n w, cLoc w x ∈ (iw w).J n → ∀ g, φ (g * x) = φ g) →
                 ∀ ψ, (∀ i, IsSmoothChar (ψ i)) → EigT φ w (iw w) ψ → CompSub π w ψ := by
  intro H L _ _ _ unr n hn V _ _ π hπ w hw φ h0 hc hJ ψ hψ he
  obtain ⟨s1, s2, -⟩ := secSpec L n w hw
  obtain ⟨τ, hτ⟩ := compEx H L unr n hn π hπ w hw
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℂ] ℂ, f ∘ φ ≠ 0 := by
    obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hg
    exact ⟨f, Function.ne_iff.2 ⟨g, hf⟩⟩
  obtain ⟨p, hp, hp0⟩ := (isoCopy _ _ _ τ.ρ _ τ.irred (isoTypic L n π hπ w hw τ hτ)).1 ⟨f ∘ φ, hc f⟩ fun h => hf (congrArg Subtype.val h)
  refine ⟨hψ, τ, hτ, locSub H _ n ψ _ τ.ρ τ.smooth τ.irred _ hp0 (fun u hu => ?_) fun d hd => ?_⟩
  · rw [← hp]
    congr 1
    exact Subtype.ext (funext fun g => congrArg f (hJ _ (s1 u) (by rwa [s2]) g))
  · rw [← dcMap (iw w) _ τ.ρ p hp, ← map_smul]
    congr 1
    apply Subtype.ext
    have a := dcMap (iw w) ((repOn hπ).comp (secW n w)) ((RU L n).comp (secW n w)) π.subtype (fun _ _ => rfl) (Sig.dg d) ⟨f ∘ φ, hc f⟩
    have b := dcMap (iw w) ((rightReg ℂ (UA L n) V).comp (secW n w)) ((RU L n).comp (secW n w)) (f.compLeft (UA L n))
      (fun _ _ => rfl) (Sig.dg d) φ
    rw [show UpperTheory.V.Hi.dc _ _ _ _ φ = _ • φ from he d hd, map_smul] at b
    exact a.trans b.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ImportsAlt
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.raise :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π →
        ∀ U : Subgroup (UA L n), U ≤ Kall L n → ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U ∧ IsUnramU π w) → ∀ (W : ∀ w : Plc L, Sig.Lev (Kw w)) (φ : UA L n → V), φ ≠ 0 → CoefIn φ π →
        IsAF R (lev U S W) φ → ∃ φ' : UA L n → V, φ' ≠ 0 ∧ CoefIn φ' π ∧ IsAF R U φ' := by
  classical
  intro L _ _ _ n V _ _ _ R π hπ U hU S
  induction S using Finset.induction_on with
  | empty => exact fun _ _ W φ h0 hc h => ⟨φ, h0, hc, h.left, h.inf, fun u hu => h.level u (by simpa [lev] using hu)⟩
  | insert w S hw ih =>
    intro hS hK W φ h0 hc h
    have hwm : w ∈ insert w S := Finset.mem_insert_self _ _
    obtain ⟨φ', a0, a1, a2⟩ := spanSph L n V π hπ w (hK w hwm).2 φ h0 hc
    obtain ⟨k1, k2, -⟩ := spanKeep L n V w φ φ' a1
    have hA : IsAF R (lev U S W ⊓ away n w) φ' := k2 R _ inf_le_right ⟨h.left, h.inf, fun u hu => h.level u (by
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hu
      simp only [lev, away, Subgroup.mem_inf, Subgroup.mem_iInf] at h1 h2 ⊢
      refine ⟨h1.1, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.1 hw' with rfl | hw'
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 (h2 w' rfl)]; exact one_mem _
      · exact h1.2 w' hw')⟩
    refine ih ⟨fun u hu => hS.split u (Finset.mem_insert_of_mem hu), hS.inj.mono (by simp)⟩
      (fun u hu => hK u (Finset.mem_insert_of_mem hu)) W φ' a0 (k1 π hπ hc) ⟨hA.left, hA.inf, fun u hu g => ?_⟩
    obtain ⟨-, f2, -, -, -, f6⟩ := factor L n w
    obtain ⟨x, hx, y, hy, rfl⟩ := f2 u
    have hxK : x ∈ Kall L n := ((f6 x hx y hy).1 (hU hu.1)).1
    have hxl : x ∈ lev U S W := by
      simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
      refine ⟨(hK w hwm).1 ⟨hx, hxK⟩, fun w' hw' => ?_⟩
      have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun e =>
        hw (hS.inj (Finset.mem_coe.2 hwm) (Finset.mem_coe.2 (Finset.mem_insert_of_mem hw')) e ▸ hw')
      have := (factor L n w').2.2.1 w hne hx
      simp only [away, Subgroup.mem_iInf] at this
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 (this w' rfl)]
      exact one_mem _
    have hyl : y ∈ lev U S W := (Subgroup.mul_mem_cancel_left _ hxl).1 hu
    rw [← mul_assoc, hA.level y ⟨hyl, hy⟩, a2 x ⟨hx, hxK⟩]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecMemLev
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem away_one {w : Plc L} {y : UA L n} (hy : y ∈ away n w) : cLoc w y = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy w) rfl)

private theorem finOrb (w : Plc L) (x : GL (Fin n) (Kw w)) :
    UpperTheory.V.AlgebraTools.FinOrb ((iw w).J n) ((iw w).J n) x :=
  ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).1 x

private theorem sec_mem_lev {U : Subgroup (UA L n)} {S : Finset (Plc L)} (hP : Places (S : Set (Plc L)))
    (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) {w : Plc L} (hw : w ∈ S) {j : GL (Fin n) (Kw w)}
    (hj : j ∈ (iw w).J n) : secW n w j ∈ lev U S iw := by
  obtain ⟨h1, h2, -, -⟩ := secSpec L n w (hP.split w (Finset.mem_coe.2 hw))
  have hK : secW n w j ∈ Kall L n := ((factor L n w).2.2.2.2.1 _ (h1 j)).2 (by
    have hKO : GlobalTheory.SplitWeil.KO (w.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL w n := GlobalTheory.SmGL.SphCompletion.KO_completion w n
    rw [h2, ← hKO]
    exact ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).2.2.2 hj)
  refine Subgroup.mem_inf.2 ⟨hS w hw ⟨h1 j, hK⟩, ?_⟩
  refine Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_
  rw [Subgroup.mem_comap]
  by_cases e : w' = w
  · subst e
    rw [h2]
    exact hj
  · have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h =>
      e (hP.inj (Finset.mem_coe.2 hw') (Finset.mem_coe.2 hw) h.symm)
    rw [away_one ((factor L n w').2.2.1 w hne (h1 j))]
    exact one_mem _

private theorem op_inSpan {w : Plc L} (hw : IsSplitAt w) (d : Fin n → (Kw w)ˣ) (φ : UA L n → V) :
    InSpan w φ (op w (iw w) d φ) := by
  haveI : Finite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n)) :=
    finOrb w _
  haveI := Fintype.ofFinite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n))
  simp only [InSpan, op, UpperTheory.V.Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span
    ⟨secW n w (q : GL (Fin n) (Kw w) ⧸ (iw w).J n).out, (secSpec L n w hw).1 _, rfl⟩

private theorem fix_of_AF {R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V} {U : Subgroup (UA L n)}
    {S : Finset (Plc L)} (hP : Places (S : Set (Plc L))) (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U)
    {w : Plc L} (hw : w ∈ S) {φ : UA L n → V} (hφ : IsAF R (lev U S iw) φ) :
    φ ∈ UpperTheory.V.Hi.fixd ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) := fun j hj =>
  funext fun g => hφ.level _ (sec_mem_lev hP hS hw hj) g

private theorem hk_val {w : Plc L} (x : GL (Fin n) (Kw w))
    (v : UpperTheory.V.Hi.fixd ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n)) :
    (UpperTheory.V.AlgebraTools.hk ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) x v : UA L n → V) =
      UpperTheory.V.Hi.dc ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) ((iw w).J n) x v :=
  (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ _ _ _ x (finOrb w x)).1 v

private theorem op_keep {R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V} {U : Subgroup (UA L n)}
    {S : Finset (Plc L)} (hP : Places (S : Set (Plc L))) (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U)
    {w : Plc L} (hw : w ∈ S) (d : Fin n → (Kw w)ˣ) {φ : UA L n → V} (hφ : IsAF R (lev U S iw) φ) :
    IsAF R (lev U S iw) (op w (iw w) d φ) := by
  have hsp := hP.split w (Finset.mem_coe.2 hw)
  obtain ⟨-, hc, hsec, -⟩ := secSpec L n w hsp
  have hA : IsAF R (lev U S iw ⊓ away n w) φ :=
    ⟨hφ.left, hφ.inf, fun u hu g => hφ.level u hu.1 g⟩
  have hB := (spanKeep L n V w φ _ (op_inSpan hsp d φ)).2.1 R _ inf_le_right hA
  have hfix : op w (iw w) d φ ∈ UpperTheory.V.Hi.fixd ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) := by
    have h := (UpperTheory.V.AlgebraTools.hk ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) (Sig.dg d)
      ⟨φ, fix_of_AF hP hS hw hφ⟩).2
    rwa [hk_val] at h
  refine ⟨hB.left, hB.inf, fun a ha g => ?_⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := (factor L n w).2.1 a
  have hxJ : cLoc w x ∈ (iw w).J n := by
    have h : cLoc w (x * y) ∈ (iw w).J n :=
      Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ha.2 w) hw)
    rwa [map_mul, away_one hy, mul_one] at h
  have hxA : x ∈ lev U S iw := by
    have h := sec_mem_lev hP hS hw hxJ
    rwa [hsec x hx] at h
  have hyA : y ∈ lev U S iw ⊓ away n w :=
    ⟨by simpa using mul_mem (inv_mem hxA) ha, hy⟩
  rw [← mul_assoc, hB.level y hyA]
  have h := congrFun (hfix _ hxJ) g
  rw [← hsec x hx]
  exact h

private theorem op_comm {w w' : Plc L} (hw : IsSplitAt w) (hw' : IsSplitAt w')
    (hne : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) (d : Fin n → (Kw w)ˣ) (d' : Fin n → (Kw w')ˣ) :
    Commute (op (V := V) w (iw w) d) (op (V := V) w' (iw w') d') := by
  haveI : Finite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n)) :=
    finOrb w _
  haveI := Fintype.ofFinite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n))
  haveI : Finite (MulAction.orbit ((iw w').J n) ((Sig.dg d' : GL (Fin n) (Kw w')) : GL (Fin n) (Kw w') ⧸ (iw w').J n)) :=
    finOrb w' _
  haveI := Fintype.ofFinite (MulAction.orbit ((iw w').J n) ((Sig.dg d' : GL (Fin n) (Kw w')) : GL (Fin n) (Kw w') ⧸ (iw w').J n))
  simp only [op, UpperTheory.V.Hi.dc, finsum_eq_sum_of_fintype]
  refine Commute.sum_left _ _ _ fun q _ => Commute.sum_right _ _ _ fun q' _ => ?_
  have hc := (factor L n w).1 _ ((secSpec L n w hw).1 (q : GL (Fin n) (Kw w) ⧸ (iw w).J n).out) _
    ((factor L n w).2.2.1 w' hne ((secSpec L n w' hw').1 (q' : GL (Fin n) (Kw w') ⧸ (iw w').J n).out))
  show _ * _ = _ * _
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, hc]

private theorem op_unit {R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V} {U : Subgroup (UA L n)}
    {S : Finset (Plc L)} (hP : Places (S : Set (Plc L))) (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U)
    {w : Plc L} (hw : w ∈ S) (d : Fin n → (Kw w)ˣ) (hd : ∀ i, d i ∈ UpperTheory.V.Hi.Uo (Kw w))
    {φ : UA L n → V} (hφ : IsAF R (lev U S iw) φ) : op w (iw w) d φ = φ := by
  have hmem : Sig.dg d ∈ (iw w).J n :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_map.2 ⟨d, fun i _ => hd i, rfl⟩))
  have hf : UpperTheory.V.AlgebraTools.FinOrb ((iw w).J n) ((iw w).J n) (1 : GL (Fin n) (Kw w)) := finOrb w 1
  set ρ := (rightReg ℂ (UA L n) V).comp (secW n w) with hρ
  have e1 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ ρ _ _ 1 hf).2.2 (Sig.dg d) hmem 1 (one_mem _)
  have e2 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ ρ _ _ 1 hf).2.1 {1}
    (fun y hy => by
      rw [Finset.mem_singleton.1 hy]
      exact MulAction.mem_orbit_self _)
    (fun q hq => by
      obtain ⟨a, rfl⟩ := hq
      refine ⟨1, ⟨Finset.mem_singleton_self _, ?_⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩
      exact (QuotientGroup.eq.2 (by simpa using a.2))) ⟨φ, fix_of_AF hP hS hw hφ⟩
  have e3 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ ρ _ _ (Sig.dg d) (finOrb w _)).1 ⟨φ, fix_of_AF hP hS hw hφ⟩
  rw [mul_one, mul_one] at e1
  rw [e1, e2] at e3
  simpa using e3.symm

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.Sym.Al.afOps :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)), U ≤ Kall L n → ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) →
        ∃ u : ∀ w : Plc L, (Fin n → (Kw w)ˣ) → Module.End ℂ (AF R (lev U S iw)),
          (∀ w ∈ S, ∀ d, AlgebraTools.Dom d → ∀ φ, ((u w d φ : AF R (lev U S iw)) : UA L n → V) = op w (iw w) d φ) ∧
          (∀ w ∈ S, ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → u w (d * d') = u w d * u w d') ∧
          (∀ w ∈ S, ∀ d, (∀ i, d i ∈ Hi.Uo (Kw w)) → u w d = 1) ∧
          ∀ w ∈ S, ∀ w' ∈ S, w ≠ w' → ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → Commute (u w d) (u w' d') := by
  intro L _ _ _ n V _ _ R U _ S hP hS
  classical
  let u : ∀ w : Plc L, (Fin n → (Kw w)ˣ) → Module.End ℂ (AF R (lev U S iw)) := fun w d =>
    if hw : w ∈ S then (op w (iw w) d).restrict (fun _ hφ => op_keep hP hS hw d hφ) else 0
  have hu : ∀ w, w ∈ S → ∀ d (φ : AF R (lev U S iw)),
      ((u w d φ : AF R (lev U S iw)) : UA L n → V) = op w (iw w) d φ := by
    intro w hw d φ
    simp only [u, dif_pos hw]
    rfl
  refine ⟨u, fun w hw d _ φ => hu w hw d φ, fun w hw d d' hd hd' => ?_, fun w hw d hd => ?_,
    fun w hw w' hw' hne d d' _ _ => ?_⟩
  · refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [hu w hw, Module.End.mul_apply, hu w hw, hu w hw]
    have h := congrArg Subtype.val (LinearMap.congr_fun
      ((Sig.hkMul (Kw w) (iw w) n (UA L n → V) ((rightReg ℂ (UA L n) V).comp (secW n w))).1 d d' hd hd')
      ⟨φ.1, fix_of_AF hP hS hw φ.2⟩)
    rw [Module.End.mul_apply, hk_val, hk_val, hk_val] at h
    exact h.symm
  · refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [hu w hw]
    exact op_unit hP hS hw d hd φ.2
  · have hne' : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) := fun h =>
      hne (hP.inj (Finset.mem_coe.2 hw') (Finset.mem_coe.2 hw) h).symm
    refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hu w hw, hu w' hw', hu w' hw', hu w hw]
    exact LinearMap.congr_fun (op_comm (hP.split w (Finset.mem_coe.2 hw)) (hP.split w' (Finset.mem_coe.2 hw')) hne' d d') _
end

