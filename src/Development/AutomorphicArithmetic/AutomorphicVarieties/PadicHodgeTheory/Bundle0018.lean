import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0014
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.CardCokernelTransposeEqCardKernel
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0042

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.UnramifiedCocycles

variable {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]

private def SD (_ρ : Representation A G V) : Type := V × G

private instance instGroupSD (ρ : Representation A G V) : Group (SD ρ) where
  mul p q := (p.1 + ρ p.2 q.1, p.2 * q.2)
  one := (0, 1)
  inv p := (-(ρ p.2⁻¹ p.1), p.2⁻¹)
  mul_assoc p q r := by
    refine Prod.ext ?_ (mul_assoc p.2 q.2 r.2)
    change p.1 + ρ p.2 q.1 + ρ (p.2 * q.2) r.1 = p.1 + ρ p.2 (q.1 + ρ q.2 r.1)
    simp [add_assoc]
  one_mul p := by
    refine Prod.ext ?_ (one_mul p.2)
    change (0 : V) + ρ 1 p.1 = p.1
    simp
  mul_one p := by
    refine Prod.ext ?_ (mul_one p.2)
    change p.1 + ρ p.2 0 = p.1
    simp
  inv_mul_cancel p := by
    refine Prod.ext ?_ (inv_mul_cancel p.2)
    change -(ρ p.2⁻¹ p.1) + ρ p.2⁻¹ p.1 = 0
    simp

private instance instTopSD (ρ : Representation A G V) [TopologicalSpace G] [TopologicalSpace V] :
    TopologicalSpace (SD ρ) := inferInstanceAs (TopologicalSpace (V × G))

private theorem topGroup_SD (ρ : Representation A G V) [TopologicalSpace G] [TopologicalSpace V]
    [IsTopologicalGroup G] [IsTopologicalAddGroup V] (h : ContAction ρ) : IsTopologicalGroup (SD ρ) := by
  have hm : Continuous fun x : (V × G) × (V × G) => ((x.1.1 + ρ x.1.2 x.2.1, x.1.2 * x.2.2) : V × G) :=
    (continuous_fst.fst.add (h.comp (continuous_fst.snd.prodMk continuous_snd.fst))).prodMk
      (continuous_fst.snd.mul continuous_snd.snd)
  have hi : Continuous fun x : V × G => ((-(ρ x.2⁻¹ x.1), x.2⁻¹) : V × G) :=
    (h.comp (continuous_snd.inv.prodMk continuous_fst)).neg.prodMk continuous_snd.inv
  exact { continuous_mul := hm, continuous_inv := hi }

private def SDsub (ρ : Representation A G V) (L : AddSubgroup V) (hL : ∀ g, ∀ y ∈ L, ρ g y ∈ L) :
    Subgroup (SD ρ) where
  carrier := {p | p.1 ∈ L}
  mul_mem' := fun {p q} hp hq => L.add_mem hp (hL _ _ hq)
  one_mem' := L.zero_mem
  inv_mem' := fun {p} hp => L.neg_mem (hL _ _ hp)

private theorem all_of_closed [TopologicalSpace G] [IsTopologicalGroup G] {I : Subgroup G} {σ : G}
    (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤) (H : Subgroup G) (hH : IsClosed (H : Set G))
    (hI : I ≤ H) (hσ : σ ∈ H) (g : G) : g ∈ H := by
  have h1 : I ⊔ Subgroup.zpowers σ ≤ H := sup_le hI (Subgroup.zpowers_le.2 hσ)
  have h2 := Subgroup.topologicalClosure_minimal _ h1 hH
  rw [hd] at h2
  exact h2 (Subgroup.mem_top g)

private theorem exists_lattice {l : ℕ} [Fact l.Prime] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [TopologicalSpace G] [CompactSpace G] (ρ : Representation A G V) (h : ContAction ρ) (x : V) :
    T2Space V ∧ TotallyDisconnectedSpace V ∧
      ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ x ∈ L ∧ ∀ g, ∀ y ∈ L, ρ g y ∈ L := by
  let e : V ≃ₗ[ℚ_[l]] (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) := (Module.finBasis ℚ_[l] V).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  let E : V ≃ₜ (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) :=
    { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := he' }
  have hT2 : T2Space V := E.isEmbedding.t2Space
  have hTD : TotallyDisconnectedSpace V :=
    E.isEmbedding.isTotallyDisconnected_range.1 (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  refine ⟨hT2, hTD, ?_⟩
  have hρc : ∀ g : G, Continuous fun v : V => ρ g v :=
    fun g => h.comp (continuous_const.prodMk continuous_id)
  have hK : IsCompact (Set.range fun g : G => e (ρ g x)) :=
    isCompact_range (he.comp (h.comp (continuous_id.prodMk continuous_const)))
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hK.isBounded
  have hr1 : Set.range (fun g : G => e (ρ g x)) ⊆ Metric.closedBall 0 (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let M := (IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank ℚ_[l] V) → ℚ_[l])
    (lt_of_lt_of_le one_pos (le_max_right r 1))).toAddSubgroup
  have hM : ∀ y, y ∈ M ↔ y ∈ Metric.closedBall (0 : Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) (max r 1) :=
    fun y => Iff.rfl
  let L : AddSubgroup V := ⨅ g : G, M.comap ((e.toLinearMap.toAddMonoidHom).comp (ρ g).toAddMonoidHom)
  have hL : ∀ v, v ∈ L ↔ ∀ g, e (ρ g v) ∈ Metric.closedBall 0 (max r 1) := by
    intro v
    simp only [L, AddSubgroup.mem_iInf, AddSubgroup.mem_comap, hM]
    rfl
  refine ⟨L, ?_, ?_, ?_⟩
  · have hcl : IsClosed (L : Set V) := by
      have : (L : Set V) = ⋂ g : G, (fun v => e (ρ g v)) ⁻¹' Metric.closedBall 0 (max r 1) := by
        ext v
        simp only [SetLike.mem_coe, hL, Set.mem_iInter, Set.mem_preimage]
      rw [this]
      exact isClosed_iInter fun g => Metric.isClosed_closedBall.preimage (he.comp (hρc g))
    have hsub : (L : Set V) ⊆ E ⁻¹' Metric.closedBall 0 (max r 1) := by
      intro v hv
      have := (hL v).1 hv 1
      simpa [E] using this
    exact (E.isCompact_preimage.2 (isCompact_closedBall _ _)).of_isClosed_subset hcl hsub
  · exact (hL x).2 fun g => hr1 ⟨g, rfl⟩
  · intro g y hy
    refine (hL _).2 fun k => ?_
    have := (hL y).1 hy (k * g)
    simpa [map_mul] using this

end UpperTheory.V.Loc.UnramifiedCocycles

open UpperTheory.V.Loc.UnramifiedCocycles in
theorem UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value :
    ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A (GQ v) V), ContAction ρ → (∀ g ∈ Iq v, ρ g = 1) → ∀ σ : GQ v, IsFrob σ → ∀ x : V, ∃! c : GQ v → V, c ∈ Z1 ρ ∧ (∀ g ∈ Iq v, c g = 0) ∧ c σ = x := by
  intro v l _ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ hc hI σ hσ x
  obtain ⟨hT2, hTD, L, hLc, hxL, hLs⟩ := exists_lattice (l := l) ρ hc x
  haveI : IsTopologicalGroup (SD ρ) := topGroup_SD ρ hc
  haveI : T2Space (SD ρ) := inferInstanceAs (T2Space (V × GQ v))
  haveI : TotallyDisconnectedSpace (SD ρ) := inferInstanceAs (TotallyDisconnectedSpace (V × GQ v))
  have hS : IsCompact ((SDsub ρ L hLs : Subgroup (SD ρ)) : Set (SD ρ)) := by
    have h0 : IsCompact ((L : Set V) ×ˢ (Set.univ : Set (GQ v))) := hLc.prod isCompact_univ
    have e0 : ((SDsub ρ L hLs : Subgroup (SD ρ)) : Set (SD ρ)) =
        ((L : Set V) ×ˢ (Set.univ : Set (GQ v)) : Set (V × GQ v)) := by
      ext p
      exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    rw [e0]
    exact h0
  haveI : CompactSpace (SDsub ρ L hLs) := isCompact_iff_compactSpace.1 hS
  obtain ⟨f, hfc, hf1, hfσ⟩ := frobFree σ hσ (SDsub ρ L hLs) ⟨((x, σ) : V × GQ v), hxL⟩
  have hfv : Continuous fun g => ((f g : SD ρ)) := continuous_subtype_val.comp hfc
  have hmul : ∀ g h, ((f (g * h) : SD ρ)) = (f g : SD ρ) * (f h : SD ρ) := fun g h => by
    rw [map_mul]
    rfl
  let k : GQ v → GQ v := fun g => ((f g : SD ρ)).2
  have hk1 : k 1 = 1 := by
    show ((f 1 : SD ρ)).2 = 1
    rw [map_one]
    rfl
  have hkm : ∀ a b, k (a * b) = k a * k b := fun a b => by
    show ((f (a * b) : SD ρ)).2 = _
    rw [hmul]
    rfl
  have hki : ∀ a, k a⁻¹ = (k a)⁻¹ := fun a => by
    have : k a⁻¹ * k a = 1 := by rw [← hkm, inv_mul_cancel, hk1]
    exact eq_inv_of_mul_eq_one_left this
  have hkc : Continuous k := continuous_snd.comp hfv
  have hgw : ∀ w : V, Continuous fun g : GQ v => ρ g w := fun w => hc.comp (continuous_id.prodMk continuous_const)
  have happ : ∀ (g : GQ v) (w : V), ρ g (ρ g⁻¹ w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have happ' : ∀ (g : GQ v) (w : V), ρ g⁻¹ (ρ g w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let H : Subgroup (GQ v) :=
    { carrier := {g | ∀ w, ρ (k g) w = ρ g w}
      one_mem' := fun w => by simp [hk1]
      mul_mem' := fun {a b} ha hb w => by
        simp only [Set.mem_setOf_eq] at ha hb
        rw [hkm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha w => by
        simp only [Set.mem_setOf_eq] at ha
        rw [hki]
        calc ρ (k a)⁻¹ w = ρ (k a)⁻¹ (ρ a (ρ a⁻¹ w)) := by rw [happ]
          _ = ρ (k a)⁻¹ (ρ (k a) (ρ a⁻¹ w)) := by rw [ha]
          _ = ρ a⁻¹ w := happ' _ _ }
  have hH : IsClosed (H : Set (GQ v)) := by
    have e1 : (H : Set (GQ v)) = ⋂ w : V, {g | ρ (k g) w = ρ g w} := by
      ext g
      simp [H]
    rw [e1]
    exact isClosed_iInter fun w => isClosed_eq ((hgw w).comp hkc) (hgw w)
  have hIH : Iq v ≤ H := fun g hg w => by
    show ρ ((f g : SD ρ)).2 w = ρ g w
    rw [hf1 g hg, hI g hg]
    show ρ (1 : GQ v) w = (1 : Module.End A V) w
    simp
  have hσH : σ ∈ H := fun w => by
    show ρ ((f σ : SD ρ)).2 w = ρ σ w
    rw [hfσ]
  have hk : ∀ g w, ρ (k g) w = ρ g w := fun g => all_of_closed (frobDense σ hσ) H hH hIH hσH g
  let c : GQ v → V := fun g => ((f g : SD ρ)).1
  have ccont : Continuous c := continuous_fst.comp hfv
  have cco : ∀ g h, c (g * h) = c g + ρ g (c h) := fun g h => by
    show ((f (g * h) : SD ρ)).1 = ((f g : SD ρ)).1 + ρ g ((f h : SD ρ)).1
    rw [hmul]
    exact congrArg (((f g : SD ρ)).1 + ·) (hk g _)
  have cI : ∀ g ∈ Iq v, c g = 0 := fun g hg => by
    show ((f g : SD ρ)).1 = 0
    rw [hf1 g hg]
    rfl
  have cσ : c σ = x := by
    show ((f σ : SD ρ)).1 = x
    rw [hfσ]
  have h1 : ∀ d : GQ v → V, (∀ g h, d (g * h) = d g + ρ g (d h)) → d 1 = 0 := fun d hd => by
    have := hd 1 1
    simpa using this
  have hinv : ∀ d : GQ v → V, (∀ g h, d (g * h) = d g + ρ g (d h)) → ∀ g, d g⁻¹ = -(ρ g⁻¹ (d g)) :=
    fun d hd g => by
      have := hd g⁻¹ g
      rw [inv_mul_cancel, h1 d hd] at this
      exact eq_neg_of_add_eq_zero_left this.symm
  refine ⟨c, ⟨⟨ccont, cco⟩, cI, cσ⟩, ?_⟩
  rintro c' ⟨hZ, hc'I, hc'σ⟩
  obtain ⟨c'cont, c'co⟩ : Continuous c' ∧ ∀ g h, c' (g * h) = c' g + ρ g (c' h) := hZ
  let H' : Subgroup (GQ v) :=
    { carrier := {g | c' g = c g}
      one_mem' := by
        show c' 1 = c 1
        rw [h1 c' c'co, h1 c cco]
      mul_mem' := fun {a b} ha hb => by
        show c' (a * b) = c (a * b)
        rw [c'co, cco, show c' a = c a from ha, show c' b = c b from hb]
      inv_mem' := fun {a} ha => by
        show c' a⁻¹ = c a⁻¹
        rw [hinv c' c'co, hinv c cco, show c' a = c a from ha] }
  have hH' : IsClosed (H' : Set (GQ v)) := isClosed_eq c'cont ccont
  have hIH' : Iq v ≤ H' := fun g hg => by
    show c' g = c g
    rw [hc'I g hg, cI g hg]
  have hσH' : σ ∈ H' := by
    show c' σ = c σ
    rw [hc'σ, cσ]
  funext g
  exact all_of_closed (frobDense σ hσ) H' hH' hIH' hσH' g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def Reach {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) (U : Submodule A V) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule A V), F 0 = ⊥ ∧ F n = U ∧ ∀ i < n, F i ≤ F (i + 1) ∧
    ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ Submodule.span A {x} ∧ ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ F i

private theorem reach_bot {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) : Reach ρ S ⊥ :=
  ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

private theorem reach_step {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {κ : G →* Aˣ} (hκ : κ ∈ S) {x : V} (hx : ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) :
    Reach ρ S (U ⊔ Submodule.span A {x}) := by
  obtain ⟨n, F, h0, hn, hs⟩ := h
  refine ⟨n + 1, fun i => if i ≤ n then F i else U ⊔ Submodule.span A {x}, by simp [h0], by simp, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · have h1 : i ≤ n := hi.le
    have h2 : i + 1 ≤ n := hi
    simp only [h1, h2, if_true]
    exact hs i hi
  · have h2 : ¬ (i + 1 ≤ i) := by omega
    simp only [h2, le_refl, if_true, if_false, hn]
    exact ⟨le_sup_left, κ, hκ, x, rfl, hx⟩

private theorem reach_fin {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {T : Set V} (hT : T.Finite) :
    (∀ x ∈ T, ∃ κ ∈ S, ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) → Reach ρ S (U ⊔ Submodule.span A T) := by
  induction T, hT using Set.Finite.induction_on with
  | empty =>
    intro _
    simpa using h
  | @insert a s ha hs ih =>
    intro hall
    have hr := ih (fun y hy => hall y (Set.mem_insert_of_mem a hy))
    obtain ⟨κ, hκ, hk⟩ := hall a (Set.mem_insert a s)
    have hr2 := reach_step hr hκ (x := a) (fun g => Submodule.mem_sup_left (hk g))
    have e : U ⊔ Submodule.span A (insert a s) = U ⊔ Submodule.span A s ⊔ Submodule.span A {a} := by
      rw [Submodule.span_insert]
      ac_rfl
    rw [e]
    exact hr2

theorem UpperTheory.filtBy_restrictScalars_of_residual_characters :
    ∀ {G E B V : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] [AddCommGroup V] [Module B V] [Module E V] [IsScalarTower E B V] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ (ρ : Representation B G V) (S : Set (G →* Eˣ)) {ι : Type} [Finite ι] (x : ι → V) (κ : ι → G →* Eˣ), Submodule.span B (Set.range x) = ⊤ → (∀ j, κ j ∈ S) → (∀ g j, ρ g (x j) - ((κ j g : Eˣ) : E) • x j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B V)) → FiltBy (resCoef E ρ) S := by
  intro G E B V _ _ _ _ _ _ _ _ _ π hπ ρ S ι _ x κ hx hκ hstep
  have hnil : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    haveI : IsNoetherianRing B := isNoetherian_of_tower E inferInstance
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact mem_nilradical.mpr (hπ a ha)
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Submodule E V, ∀ k,
      M k = ((RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V)).restrictScalars E :=
    ⟨_, fun _ => rfl⟩
  have hMm : ∀ k v, v ∈ M k ↔ v ∈ (RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V) := by
    intro k v
    rw [hM, Submodule.restrictScalars_mem]
  have down : ∀ p, Reach (resCoef E ρ) S (M (p + 1)) → Reach (resCoef E ρ) S (M p) := by
    intro p h
    have hfg : (((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E).FG := IsNoetherian.noetherian _
    obtain ⟨s, hsf, hs⟩ := Submodule.fg_def.mp hfg
    have hsub : ∀ a ∈ s, a ∈ (RingHom.ker (π : B →+* E)) ^ p := fun a ha => by
      have : a ∈ ((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E := hs ▸ Submodule.subset_span ha
      exact this
    have hTf : (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)).Finite :=
      hsf.image2 _ Set.finite_univ
    have hr := reach_fin (ρ := resCoef E ρ) (S := S) h hTf (by
      rintro y ⟨a, ha, j, -, rfl⟩
      refine ⟨κ j, hκ j, fun g => ?_⟩
      rw [hMm]
      show ρ g (a • x j) - ((κ j g : Eˣ) : E) • (a • x j) ∈
        ((RingHom.ker (π : B →+* E)) ^ (p + 1) • (⊤ : Submodule B V))
      rw [map_smul, smul_comm ((κ j g : Eˣ) : E) a, ← smul_sub, pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul (hsub a ha) (hstep g j))
    have claim : ∀ n ∈ Submodule.span B (Set.range x), ∀ a ∈ (RingHom.ker (π : B →+* E)) ^ p,
        a • n ∈ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        intro a ha
        have ha' : a ∈ Submodule.span E s := by
          rw [hs]
          exact ha
        clear ha
        induction ha' using Submodule.span_induction with
        | mem b hb => exact Submodule.subset_span ⟨b, hb, j, trivial, rfl⟩
        | zero => simp
        | add b c _ _ hb hc =>
          rw [add_smul]
          exact add_mem hb hc
        | smul c b _ hb =>
          rw [smul_assoc]
          exact Submodule.smul_mem _ c hb
      | zero => intro a _; simp
      | add y z _ _ hy hz =>
        intro a ha
        rw [smul_add]
        exact add_mem (hy a ha) (hz a ha)
      | smul b y _ hy =>
        intro a ha
        rw [smul_smul]
        exact hy (a * b) (Ideal.mul_mem_right b _ ha)
    have e : M p = M (p + 1) ⊔ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      apply le_antisymm
      · intro v hv
        apply Submodule.mem_sup_right
        rw [hMm] at hv
        refine Submodule.smul_induction_on hv ?_ ?_
        · intro a ha n _
          exact claim n (by rw [hx]; trivial) a ha
        · intro y z hy hz
          exact add_mem hy hz
      · refine sup_le ?_ ?_
        · intro v hv
          rw [hMm] at hv ⊢
          exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ p)) hv
        · rw [Submodule.span_le]
          rintro y ⟨a, ha, j, -, rfl⟩
          show a • x j ∈ M p
          rw [hMm]
          exact Submodule.smul_mem_smul (hsub a ha) trivial
    rw [e]
    exact hr
  have base : M N = ⊥ := by
    rw [hM, hN, Submodule.zero_eq_bot, Submodule.bot_smul, Submodule.restrictScalars_bot]
  have all : ∀ k, Reach (resCoef E ρ) S (M (N - k)) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.sub_zero, base]
      exact reach_bot _ _
    | succ k ih =>
      rcases Nat.lt_or_ge k N with hk | hk
      · have e : N - k = (N - (k + 1)) + 1 := by omega
        rw [e] at ih
        exact down _ ih
      · have e : N - (k + 1) = N - k := by omega
        rw [e]
        exact ih
  have top : M 0 = ⊤ := by
    rw [hM, pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.restrictScalars_top]
  have fin := all N
  rw [Nat.sub_self, top] at fin
  exact fin
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteLevelOfFiniteLevelMod
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem killed (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] :
    ∃ r : ℕ, 0 < r ∧ ∀ x : M, (l : ℤ_[l]) ^ r • x = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe12.killed l M

private theorem H0dual_eq {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V] (χ : G →* Aˣ)
    (ρ : Representation A G V) : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
  ext f
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hf
    have : coSub χ ρ ≤ LinearMap.ker f := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, x, rfl⟩
      have := hf g x
      simp [this]
    exact fun w hw => this hw
  · intro hf g x
    have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
    rw [map_sub, map_smul, sub_eq_zero] at this
    exact this

private theorem card_co {G Q A V : Type} [Group G] [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup V]
    [Module A V] [Module Q V] [IsScalarTower Q A V] (hs : Function.Surjective (algebraMap Q A)) (χ : G →* Qˣ)
    (χ' : G →* Aˣ) (h : ∀ g, ((χ' g : Aˣ) : A) = algebraMap Q A (χ g : Qˣ))
    (ρ : Representation A G V) : Nat.card (V ⧸ coSub χ' ρ) = Nat.card (V ⧸ coSub χ (resCoef Q ρ)) := by
  have e : coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
    unfold coSub
    rw [Submodule.restrictScalars_span Q A hs]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, h, algebraMap_smul]
    rfl
  rw [e]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv Q (coSub χ' ρ)).toEquiv.symm

private def modRep (n : ℕ) {G Q V : Type} [Group G] [CommRing Q] [AddCommGroup V] [Module Q V] [Module (ZMod n) V]
    (ρ : Representation Q G V) : Representation (ZMod n) G V where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem UpperTheory.finite_level_of_finite_level_mod :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ), FinLevelMod l G χ d → FinLevel l G χ d := by
  intro l _ G _ _ χ d h M _ _ _ _ _ ρ hρ
  obtain ⟨r, hr, hk⟩ := killed l M
  have hk' : ∀ x : M, (l ^ r) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]; exact hk x
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) M) := ⟨AddCommGroup.zmodModule hk'⟩
  letI : Algebra ℤ_[l] (ZMod (l ^ r)) := (PadicInt.toZModPow r).toAlgebra
  have hs : Function.Surjective (algebraMap ℤ_[l] (ZMod (l ^ r))) := ZMod.ringHom_surjective _
  haveI : IsScalarTower ℤ_[l] (ZMod (l ^ r)) M := by
    refine IsScalarTower.of_algebraMap_smul fun a x => ?_
    obtain ⟨k, hk2⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZModPow r a)
    have h0 : a - k ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hk2, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h0
    obtain ⟨b, hb⟩ := h0
    change PadicInt.toZModPow r a • x = a • x
    rw [← hk2, Nat.cast_smul_eq_nsmul, eq_add_of_sub_eq hb.symm, add_smul, mul_smul, hk, smul_zero, zero_add,
      Nat.cast_smul_eq_nsmul]
  let ρ' : Representation (ZMod (l ^ r)) G M := modRep (l ^ r) ρ
  have e : resCoef ℤ_[l] ρ' = ρ := by ext; rfl
  obtain ⟨a1, a2, a3, a4, a5⟩ := h r hr M ρ' hρ
  obtain ⟨⟨e0⟩, ⟨e1⟩, ⟨e2⟩, en⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ'
  rw [← e]
  refine ⟨Finite.of_equiv _ e1.toEquiv.symm, Finite.of_equiv _ e2.toEquiv.symm, fun n hn => ?_, ?_, ?_⟩
  · obtain ⟨e'⟩ := en n
    have := a3 n hn
    exact e'.toEquiv.subsingleton
  · rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, a4]
  · rw [Nat.card_congr e2.toEquiv, a5, H0dual_eq,
      ← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator _).toEquiv]
    have : Finite (M ⧸ coSub ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) ρ') :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    rw [KStar.Selmer.card_dual_of_baer KStar.Selmer.zmod_baer]
    exact card_co hs χ _ (fun g => rfl) ρ'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RankCohomologyRationalEqRankLattice
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.rank_cohomology_rational_eq_rank_lattice :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] G V), ContAction ρ → ∀ {n : ℕ} (ρT : Representation ℤ_[l] G (Fin n → ℤ_[l])) (j : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] V), ContAction ρT → IsOpenEmbedding j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → Module.rank ℚ_[l] ↥(H0 ρ) = Module.rank ℤ_[l] ↥(H0 ρT) ∧ Module.rank ℚ_[l] (H1 ρ) = Module.rank ℤ_[l] (H1 ρT) ∧ Module.rank ℚ_[l] (H2 ρ) = Module.rank ℤ_[l] (H2 ρT) := by
  intro l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ n ρT j hT hj he hm
  haveI : ContinuousConstSMul ℤ_[l] V := ⟨fun c => by
    have h : (fun x : V => c • x) = fun x => (algebraMap ℤ_[l] ℚ_[l] c) • x :=
      funext fun x => (algebraMap_smul ℚ_[l] c x).symm
    rw [h]
    exact continuous_const_smul _⟩
  let L : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := Fin n → ℤ_[l], rho := ρT, cont := hT }
  let U : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := V, rho := resCoef ℤ_[l] ρ, cont := hρ }
  let P : ReciprocityTheory.Coh.Pair L U := ⟨MonoidHom.id G, j, continuous_id, hj.continuous, he⟩
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl' : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hloc := ReciprocityTheory.Coh.localise_holds ℤ_[l] G (l : ℤ_[l]) L U P rfl hj
    ⟨Homeomorph.smulOfNeZero (α := V) (l : ℚ_[l]) hl, fun (v : V) => by
      show (l : ℚ_[l]) • v = (l : ℤ_[l]) • v
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]⟩ hm
  have hp : Submonoid.powers (l : ℤ_[l]) ≤ nonZeroDivisors ℤ_[l] :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hl'
  have hr : ∀ k, Module.rank ℤ_[l] (U.H k) = Module.rank ℤ_[l] (L.H k) := fun k =>
    haveI := hloc k
    IsLocalizedModule.rank_eq (Submonoid.powers (l : ℤ_[l])) hp (P.hom.H k)
  obtain ⟨a₀, a₁, a₂, -⟩ := ReciprocityTheory.Coh.exists_isLow L
  obtain ⟨b₀, b₁, b₂, -⟩ := ReciprocityTheory.Coh.exists_isLow U
  obtain ⟨⟨c₀⟩, ⟨c₁⟩, ⟨c₂⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ
  refine ⟨?_, ?_, ?_⟩
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₀.trans c₀).rank_eq.symm.trans ((hr 0).trans a₀.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₁.trans c₁).rank_eq.symm.trans ((hr 1).trans a₁.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₂.trans c₂).rank_eq.symm.trans ((hr 2).trans a₂.rank_eq)
end

