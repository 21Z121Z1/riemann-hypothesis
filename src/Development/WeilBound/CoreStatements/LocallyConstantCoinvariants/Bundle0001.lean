import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.TopOfMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
section
noncomputable section

namespace PositivityTheory.KCo

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

open Classical in

def extZ : SB (RankIn k (Fin n) (Fin d) {n}) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun φ Y := if h : Yᵀ.rank = n then φ.1 ⟨Yᵀ, h⟩ else 0
  map_add' φ ψ := funext fun Y => by by_cases h : Yᵀ.rank = n <;> simp [h, -rank_transpose]
  map_smul' c φ := funext fun Y => by by_cases h : Yᵀ.rank = n <;> simp [h, -rank_transpose]

theorem extZ_pos (φ : SB (RankIn k (Fin n) (Fin d) {n})) {Y : Matrix (Fin n) (Fin d) k} (h : Yᵀ.rank = n) :
    extZ φ Y = φ.1 ⟨Yᵀ, h⟩ := dif_pos h

theorem extZ_neg (φ : SB (RankIn k (Fin n) (Fin d) {n})) {Y : Matrix (Fin n) (Fin d) k} (h : Yᵀ.rank ≠ n) :
    extZ φ Y = 0 := dif_neg h

theorem isOpenEmb : IsOpenEmbedding fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ := by
  have hXo : IsOpen {x : Matrix (Fin d) (Fin n) k | x.rank ∈ ({n} : Set ℕ)} := by
    convert isOpen_le_rank (k := k) (a := Fin n) (b := Fin d) n using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => h.ge, fun h => le_antisymm (Matrix.rank_le_width x) h⟩
  let T : Matrix (Fin d) (Fin n) k ≃ₜ Matrix (Fin n) (Fin d) k :=
    { toFun := transpose, invFun := transpose, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      continuous_toFun := continuous_id.matrix_transpose, continuous_invFun := continuous_id.matrix_transpose }
  exact T.isOpenEmbedding.comp hXo.isOpenEmbedding_subtypeVal

theorem extZ_mem (φ : SB (RankIn k (Fin n) (Fin d) {n})) : extZ φ ∈ SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hi := isOpenEmb (k := k) (n := n) (d := d)
  have hC : IsCompact ((fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ) '' tsupport φ.1) := φ.2.2.image hi.continuous
  have h0 : ∀ Y ∉ (fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ) '' tsupport φ.1, extZ φ Y = 0 := fun Y hY => by
    by_cases h : Yᵀ.rank = n
    · rw [extZ_pos φ h]
      exact image_eq_zero_of_notMem_tsupport fun hm => hY ⟨_, hm, rfl⟩
    · exact extZ_neg φ h
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun Y => ?_, HasCompactSupport.intro hC h0⟩
  by_cases h : Yᵀ.rank = n
  · have e := hi.map_nhds_eq ⟨Yᵀ, h⟩
    rw [transpose_transpose] at e
    rw [← e, Filter.eventually_map, extZ_pos φ h]
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 φ.2.1 ⟨Yᵀ, h⟩] with x hx
    rw [extZ_pos φ (Y := x.1ᵀ) x.2]
    exact hx
  · have hY : Y ∉ (fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ) '' tsupport φ.1 := by
      rintro ⟨x, -, rfl⟩
      exact h x.2
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hY] with Z hZ
    rw [h0 Z hZ, h0 Y hY]

theorem exists_extZ {Φ : Matrix (Fin n) (Fin d) k → ℂ} (h : Full Φ) : ∃ φ, extZ φ = Φ := by
  refine ⟨⟨_, comp_mem_SB_of_isInducing (isOpenEmb (k := k) (n := n) (d := d)).isInducing ⟨Φ, h.1⟩ isClosed_univ (fun _ => trivial)
    fun Y _ hY => ⟨⟨Yᵀ, (rank_transpose Y).trans (not_not.1 fun e => hY (h.2 Y e))⟩, rfl⟩⟩, funext fun Y => ?_⟩
  by_cases hY : Yᵀ.rank = n
  · exact extZ_pos _ hY
  · rw [extZ_neg _ hY, h.2 Y (by rwa [rank_transpose] at hY)]

theorem extZ_act (μ : kˣ →* ℂˣ) (g : GL (Fin n) k) (h : GL (Fin d) k) (φ : SB (RankIn k (Fin n) (Fin d) {n}))
    (Y : Matrix (Fin n) (Fin d) k) : extZ (omegaOn (Fin n) (Fin d) μ {n} (g, h) φ) Y =
      (omChar (Fin n) (Fin d) μ (g, h) : ℂ) * extZ φ (g.valᵀ * Y * (invT h).val) := by
  have e : (g.valᵀ * Y * (invT h).val)ᵀ = act Yᵀ (g, h) := by
    simp only [act, invT, transpose_mul, MonoidHom.coe_mk, OneHom.coe_mk, transpose_transpose, Matrix.mul_assoc]
  by_cases hY : Yᵀ.rank = n
  · rw [extZ_pos _ hY, extZ_pos φ (by rw [e, rank_act]; exact hY)]
    exact congrArg (fun x => (omChar (Fin n) (Fin d) μ (g, h) : ℂ) * φ.1 x) (Subtype.ext e.symm)
  · rw [extZ_neg _ hY, extZ_neg φ (by rw [e, rank_act]; exact hY), mul_zero]

theorem irr_equiv {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {τ : Representation ℂ (Γ × G) V} {τ' : Representation ℂ (Γ × G) U} (E : τ.Equiv τ')
    (H : ∀ N : Submodule ℂ U, twRel (τ'.comp (MonoidHom.inl _ _)) 1 ≤ N → (∀ h, ∀ f ∈ N, τ' (1, h) f ∈ N) →
      N = ⊤ ∨ N ≤ twRel (τ'.comp (MonoidHom.inl _ _)) 1)
    (N : Submodule ℂ V) (hR : twRel (τ.comp (MonoidHom.inl _ _)) 1 ≤ N) (hN : ∀ h, ∀ f ∈ N, τ (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel (τ.comp (MonoidHom.inl _ _)) 1 := by
  have hE : ∀ γ φ, E.toLinearEquiv (τ γ φ) = τ' γ (E.toLinearEquiv φ) := fun γ φ => LinearMap.congr_fun (E.isIntertwining' γ) φ
  have h1 : twRel (τ'.comp (MonoidHom.inl _ _)) 1 ≤ (twRel (τ.comp (MonoidHom.inl _ _)) 1).map E.toLinearEquiv.toLinearMap :=
    Submodule.span_le.2 (by
      rintro _ ⟨g, f, rfl⟩
      obtain ⟨φ, rfl⟩ := E.toLinearEquiv.surjective f
      exact ⟨_, Submodule.subset_span ⟨g, φ, rfl⟩, by rw [map_sub, map_smul]; exact congrArg (· - _) (hE (g, 1) φ)⟩)
  rcases H (N.map E.toLinearEquiv.toLinearMap) (h1.trans (Submodule.map_mono hR)) (by
    rintro h _ ⟨f, hf, rfl⟩
    exact ⟨_, hN h f hf, hE _ f⟩) with h | h
  · exact Or.inl (top_of_map E.toLinearEquiv.toLinearMap (R := ⊥) (fun f hf => E.toLinearEquiv.map_eq_zero_iff.1 hf) bot_le h)
  · refine Or.inr fun f hf => ?_
    obtain ⟨g, hg, e⟩ := h1 (h ⟨f, hf, rfl⟩)
    rwa [← E.toLinearEquiv.injective e]

theorem irrSt_of (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : IrrSt := by
  intro k _ _ _ _ n d ν α hnd hν hα N hA hN
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnd
  have hμ : IsSmoothChar ν⁻¹ := IsSmoothChar.inv hν.2
  obtain ⟨E⟩ := GlobalTheory.T.omega_equiv_induced_fibre k (Fin n) (Fin (n + t)) (Fin n) (Fin t) (stdSum rfl) n (Fintype.card_fin n).symm ν⁻¹ hμ
  have hR : twRel ((omegaOn (Fin n) (Fin (n + t)) ν⁻¹ {n}).comp (MonoidHom.inl _ _)) 1 ≤
      (aug n (n + t) ν α).comap extZ := Submodule.span_le.2 (by
    rintro _ ⟨g, φ, rfl⟩
    refine Submodule.subset_span ⟨g, extZ φ, extZ_mem φ, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    congr 1
    refine funext fun Y => (extZ_act _ g 1 φ Y).trans ?_
    have n1 : nabs k 1 = 1 := by simp [nabs]
    simp [omB, omChar, apow, val_absPow, n1])
  rcases irr_equiv E (irr_ind hB n t hμ (fun y => by simp [hν.1 y])) (N.comap extZ) (hR.trans (Submodule.comap_mono hA)) (by
    intro h φ hf
    have h1 := hN (invT h) _ hf (extZ_mem φ)
    rw [Submodule.mem_comap]
    have c0 : (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero (absPow k ((n : ℂ) / 2) (gdet (invT h))))
    convert N.smul_mem ((omChar (Fin n) (Fin (n + t)) ν⁻¹ (1, h) : ℂ) /
      ((α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2))) h1 using 1
    funext Y
    have e1 : omB ν α 1 (invT h) (extZ φ) Y = (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) *
        extZ φ ((1 : GL (Fin n) k).valᵀ * Y * (invT h).val) := by
      simp [omB, apow, nabs]
    rw [extZ_act, Pi.smul_apply, e1, smul_eq_mul, ← mul_assoc, div_mul_cancel₀ _ c0]) with h | h
  · refine Or.inl fun Φ hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact (h ▸ Submodule.mem_top : φ ∈ N.comap extZ)
  · refine Or.inr fun Φ hm hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact hR (h hm)

end PositivityTheory.KCo
end
end

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull
section
noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {om : Rep σ X W} {v : Pl F}
  {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {ν α : (Fv F v)ˣ →* ℂˣ}

theorem augAt_le : augAt om v ≤ SB _ := Submodule.span_le.2 (by
  rintro _ ⟨g, -, φ, h, φ₁, h₁, -, rfl⟩
  exact sub_mem h₁ h)

theorem aug_le_map (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) : aug n d ν α ≤ (augAt om v).map ι := Submodule.span_le.2 (by
  rintro _ ⟨g₀, Φ, hΦ, rfl⟩
  obtain ⟨φ, hφ, rfl⟩ := hb.2.2 hΦ
  obtain ⟨g, hg, h⟩ := hD.leftOnto g₀
  obtain ⟨φ₁, h₁, ha, e⟩ := h φ hφ
  exact ⟨φ₁ - φ, Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, h₁, ha, rfl⟩, by rw [map_sub, e]⟩)

theorem mem_augAt (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (h : ι φ ∈ aug n d ν α) : φ ∈ augAt om v := by
  obtain ⟨ψ, hψ, e⟩ := aug_le_map hb hD h
  rwa [← hb.2.1 (augAt_le hψ) hφ e]

theorem exists_full (hS : SurjSt) (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) (hν : USm ν) (h1 : ν ≠ 1) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), Full (ι φ₀) ∧ φ - φ₀ ∈ augAt om v := by
  obtain ⟨Φ₀, h0, h⟩ := hS _ n d ν α hν h1 _ (hb.1 hφ)
  obtain ⟨φ₀, hφ₀, rfl⟩ := hb.2.2 h0.1
  exact ⟨φ₀, hφ₀, h0, mem_augAt hb hD (sub_mem hφ hφ₀) (by rwa [map_sub])⟩

theorem ker_eq (hS : SurjSt) (hI : IrrSt) (hnd : n ≤ d)
    (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) (hν : USm ν) (hα : USm α) (h1 : ν ≠ 1) {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P) (onto : (SB _).map p = ⊤) (inv : augAt om v ≤ LinearMap.ker p)
    (st : ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → p φ = 0 → p φ₁ = 0) :
    ∀ φ ∈ SB _, p φ = 0 ↔ φ ∈ augAt om v := by
  intro φ hφ
  refine ⟨fun h0 => ?_, fun h => inv h⟩
  rcases hI _ n d ν α hnd hν hα ((SB _ ⊓ LinearMap.ker p).map ι)
    ((aug_le_map hb hD).trans (Submodule.map_mono (le_inf augAt_le inv))) (by
      rintro h₀ _ ⟨ψ, hψ, rfl⟩ -
      obtain ⟨h, hh, hr⟩ := hD.rightOnto h₀
      obtain ⟨ψ₁, h₁, ha, e⟩ := hr ψ hψ.1
      exact ⟨ψ₁, ⟨h₁, st h hh ψ hψ.1 ψ₁ h₁ ha hψ.2⟩, e⟩) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    obtain ⟨ψ, hψ, rfl⟩ : x ∈ (SB _).map p := onto ▸ Submodule.mem_top
    obtain ⟨ψ₀, h₀, hf, ha⟩ := exists_full hS hb hD hν h1 hψ
    obtain ⟨χ, hχ, e⟩ := h _ hf
    have e' : χ = ψ₀ := hb.2.1 hχ.1 h₀ e
    have h2 : p (ψ - ψ₀) = 0 := inv ha
    have h3 : p ψ₀ = 0 := e' ▸ hχ.2
    exact hx (by rwa [map_sub, h3, sub_zero] at h2)
  · obtain ⟨φ₀, h₀, hf, ha⟩ := exists_full hS hb hD hν h1 hφ
    have h2 : p (φ - φ₀) = 0 := inv ha
    have h3 : p φ₀ = 0 := by rwa [map_sub, h0, zero_sub, neg_eq_zero] at h2
    have := add_mem ha (mem_augAt hb hD h₀ (h _ ⟨φ₀, ⟨h₀, h3⟩, rfl⟩ hf))
    rwa [sub_add_cancel] at this

theorem acts_zero (γ : UA σ X.J × UA σ W.J) : Acts (evFin F v) (om γ) (0 : (Fin n × Fin d → Fv F v) → ℂ) 0 := fun r _ => by
  have : tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [this, map_zero]

theorem chrW_div_ne {χ χ' : Chr F E} {t : E →ₐ[F] Fv F v} (h : chrW (χ / χ') t ≠ 1) : chrW (χ' / χ) t ≠ 1 := fun e =>
  h (MonoidHom.ext fun x => by
    have := DFunLike.congr_fun e x
    simp only [chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.one_apply] at this ⊢
    rw [map_div, div_eq_one] at this ⊢
    exact this.symm)

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩

def GoodSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v)

theorem kCoinv_of (hS : SurjSt) (hI : IrrSt) (hD : DictSt) (hN : NuSt) (hSo : SoSt) (hG : GoodSplit) : GlobalTheory.ThK.KCoinv := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  have hT := hM.triple
  have hF := hM.fin
  refine ⟨fun v hv => ?_, hSo F E σ B a a' G X om om' hT⟩
  have ha' : 1 ≤ a' := by have := hT.geo.aBig; omega
  have ha : 1 ≤ a := by have := hT.geo.lt; omega
  have D1 := fun t => hD F E σ _ _ B G.V G.W G.M om _ _ hT.base ⟨_, _, hT.geo.hV⟩ ⟨_, _, hT.geo.hW⟩ hT.geo.hM hT.weil
    hT.chars.heckeβ (isHecke_div hT.chars.heckeβ hT.chars.heckeα) v t
  have D2 := fun t => hD F E σ _ _ B G.V' G.W G.M' om' _ _ hT.base ⟨_, _, hT.geo.hV'⟩ ⟨_, _, hT.geo.hW⟩ hT.geo.hM' hT.weil'
    hT.chars.heckeα (isHecke_div hT.chars.heckeα hT.chars.heckeβ) v t
  have hn := hN F E σ B a a' G X om om' hT v hv
  have := hF.nontriv v
  obtain ⟨t₀⟩ : Nonempty (E →ₐ[F] Fv F v) := hG F E σ B hT.base v hv.2
  have k2 : ∀ φ ∈ SB _, Rf.p' v φ = 0 ↔ φ ∈ augAt om' v := by
    obtain ⟨⟨ι, hι⟩, ν, α, hν, hα, h1, h⟩ := D2 t₀
    exact ker_eq hS hI (by omega) hι.bij (h ι hι) hν hα (fun e => (h1 ha' (by omega) e).elim (hn _) (hn _)) _ (hF.onto' v) (hF.inv' v)
      fun g hg φ hφ φ₁ h₁ hA h0 => by
        simpa using (hF.equiv v g hg 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ h₁ (acts_zero _) hA (by simp [h0])).symm
  refine ⟨?_, k2, fun t ξ => ?_, fun l hl => ?_⟩
  · obtain ⟨⟨ι, hι⟩, ν, α, hν, hα, h1, h⟩ := D1 t₀
    exact ker_eq hS hI (by omega) hι.bij (h ι hι) hν hα
      (fun e => (h1 ha (by omega) e).elim (chrW_div_ne (hn _)) (chrW_div_ne (hn _))) _ (hF.onto v) (hF.inv v)
      fun g hg φ hφ φ₁ h₁ hA h0 => by
        simpa using hF.equiv v g hg φ hφ 0 (zero_mem _) φ₁ h₁ 0 (zero_mem _) hA (acts_zero _) (by simp [h0])
  · obtain ⟨⟨ι, hι⟩, ν, α, hν, hα, h1, h⟩ := D2 t
    obtain ⟨ψ, hψ, rfl⟩ : ξ ∈ (SB _).map (Rf.p' v) := hF.onto' v ▸ Submodule.mem_top
    obtain ⟨ψ₀, h₀, hf, hA⟩ := exists_full hS hι.bij (h ι hι) hν (fun e => (h1 ha' (by omega) e).elim (hn _) (hn _)) hψ
    have h2 : Rf.p' v (ψ - ψ₀) = 0 := hF.inv' v hA
    exact ⟨ψ₀, ⟨h₀, ι, hι, hf.2⟩, by rw [map_sub, sub_eq_zero] at h2; exact h2.symm⟩
  · let q := (Rf.p' v).domRestrict (SB _)
    have hq : LinearMap.range q = ⊤ := by rw [LinearMap.range_domRestrict, hF.onto' v]
    obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective hq
    refine ⟨(l.domRestrict (SB _)).comp s, fun φ hφ => ?_⟩
    have e : Rf.p' v (s (Rf.p' v φ) : _) = Rf.p' v φ := LinearMap.congr_fun hs _
    have h0 : l (φ - (s (Rf.p' v φ) : _)) = 0 :=
      hl ((k2 _ (sub_mem hφ (s _).2)).1 (by rw [map_sub, e, sub_self]))
    rw [map_sub, sub_eq_zero] at h0
    exact h0

end PositivityTheory.KCo
end
end

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfFree
section
noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eq_one_of_smul [IsGalois ℚ E] {v : Pl F} (hv : SplitsFully E v) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (g : Gal(E/ℚ)) (h : g • P = P) : g = 1 := by
  haveI : P.LiesOver (v.asIdeal.under ℤ) := ⟨by rw [P.over_def v.asIdeal, Ideal.under_under]⟩
  have h1 := MulAction.index_stabilizer Gal(E/ℚ) P
  rw [Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 E) Gal(E/ℚ) (v.asIdeal.under ℤ) P, hv,
    ← IsGalois.card_aut_eq_finrank] at h1
  have h2 := (MulAction.stabilizer Gal(E/ℚ) P).card_mul_index
  rw [h1] at h2
  have h3 : Nat.card (MulAction.stabilizer Gal(E/ℚ) P) = 1 :=
    (mul_left_eq_self₀.1 h2).resolve_right Nat.card_pos.ne'
  exact (Subgroup.mem_bot).1 (Subgroup.card_eq_one.1 h3 ▸ (MulAction.mem_stabilizer_iff.2 h))

def conjQ (h : IsCMExt F E σ) : Gal(E/ℚ) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (σ : E →+* E)
    (Function.Involutive.bijective (f := σ) (cm_conj_conj h))) fun x => by simp

theorem conjQ_apply (h : IsCMExt F E σ) (x : E) : conjQ h x = σ x := rfl

end PositivityTheory.KCo
end
end

