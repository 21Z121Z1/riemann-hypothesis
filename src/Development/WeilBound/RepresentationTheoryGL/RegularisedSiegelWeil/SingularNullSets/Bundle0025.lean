import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.MemIntROfFinPart
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.NormDetLeFactorialMulProd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0022
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0024

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem fullRank_col (D : D7) (a n n₀ : ℕ) (hn₀ : 0 < n₀) (f : SchwartzMap (D.what₂.Tau → Fin a → Fin n → ℂ) ℂ) :
    ∃ C : ℝ, ∀ B : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ, (∀ τ, ‖(B τ).det‖ = 1) →
      ∑' ξ : {ξ : Matrix (Fin a) (Fin n) D.host.E // ξ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * ξ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D},
        ‖f (fun τ => B τ * ξ.1.map (tauE D τ))‖ₑ ≤ ENNReal.ofReal C := by
  haveI := GlobalTheory.CompanionTheory.Ipf.Bdd.nonempty_tau D
  obtain ⟨e, he⟩ : ∃ e : (D.what₂.Tau → Fin n → Fin a → ℂ) ≃ₗ[ℝ] (D.what₂.Tau → Fin a → Fin n → ℂ),
      ∀ x τ i j, e x τ i j = x τ j i :=
    ⟨{ toFun := fun x τ i j => x τ j i
       invFun := fun y τ j i => y τ i j
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl }, fun _ _ _ _ => rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Twist.FullRank.tsum_schwartz_fullRank_le D.host.E (GlobalTheory.CompanionTheory.Ipf.Bdd.intR D)
    D.what₂.Tau (tauE D) (fun z hz h0 => GlobalTheory.CompanionTheory.Ipf.Bdd.one_le_prod_tauE z hz h0) a n n₀ hn₀
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e.toContinuousLinearEquiv f)
  refine ⟨C, fun B hB => ?_⟩
  have hBt : ∀ τ, ‖(B τ)ᵀ.det‖ = 1 := fun τ => by
    rw [Matrix.det_transpose]
    exact hB τ
  obtain ⟨T, hT⟩ : ∃ T : {γ : Matrix (Fin n) (Fin a) D.host.E //
        γ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * γ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D} ≃
      {ξ : Matrix (Fin a) (Fin n) D.host.E //
        ξ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * ξ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D},
      ∀ γ, (T γ).1 = γ.1ᵀ :=
    ⟨{ toFun := fun γ => ⟨γ.1ᵀ, by rw [Matrix.rank_transpose]; exact γ.2.1, fun i j => γ.2.2 j i⟩
       invFun := fun ξ => ⟨ξ.1ᵀ, by rw [Matrix.rank_transpose]; exact ξ.2.1, fun i j => ξ.2.2 j i⟩
       left_inv := fun γ => Subtype.ext (Matrix.transpose_transpose _)
       right_inv := fun ξ => Subtype.ext (Matrix.transpose_transpose _) }, fun _ => rfl⟩
  rw [← T.tsum_eq]
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hC (fun τ => (B τ)ᵀ) hBt)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  congr 2
  funext τ i j
  rw [LinearEquiv.coe_toContinuousLinearEquiv']
  refine Eq.trans ?_ (he _ τ i j).symm
  rw [hT]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mul_comm]

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem tsum_GQ (V : HSp D) (n : ℕ) (γ : GA D V) (hγ : γ ∈ GQ V) (F : Mx D V.rank n → ℝ≥0∞) :
    ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (mm (mt V γ) (rat x.1)) =
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (rat x.1) := by
  obtain ⟨g, hg⟩ := mem_ratMx.1 ((mem_GQ_iff V γ).1 hγ)
  obtain ⟨g', hg'⟩ := mem_ratMx.1 ((mem_GQ_iff V γ⁻¹).1 (inv_mem hγ))
  have h1 : g' * g = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_inv_mul V γ)
  have h2 : g * g' = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_mul_inv V γ)
  have hu : IsUnit g.det := isUnit_iff_exists_inv.2 ⟨g'.det, by rw [← Matrix.det_mul, h2, Matrix.det_one]⟩
  have hu' : IsUnit g'.det := isUnit_iff_exists_inv.2 ⟨g.det, by rw [← Matrix.det_mul, h1, Matrix.det_one]⟩
  let e : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} ≃
      {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} :=
    { toFun := fun x => ⟨g * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g x.1 hu]; exact x.2⟩
      invFun := fun x => ⟨g' * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g' x.1 hu']; exact x.2⟩
      left_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h1, Matrix.one_mul])
      right_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]) }
  rw [← e.tsum_eq (fun x => F (rat x.1))]
  refine tsum_congr fun x => ?_
  show F _ = F (rat (g * x.1))
  rw [rat_mul, hg]

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_intOpen (V : HSp D) : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
    ∀ k ∈ U, ∀ i j, finPart D (mt V k i j) ∈ intAE D := by
  have hfc : Continuous (finPart D) := GlobalTheory.Member.continuous_finPart D
  have hint : ∀ (A B : Mx D V.rank V.rank), (∀ i j, finPart D (A i j) ∈ intAE D) → (∀ i j, finPart D (B i j) ∈ intAE D) →
      ∀ i j, finPart D ((A * B) i j) ∈ intAE D := by
    intro A B hA hB i j
    rw [Matrix.mul_apply, map_sum]
    exact sum_mem fun l _ => by rw [map_mul]; exact GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hA i l) (hB l j)
  have hone : ∀ i j, finPart D ((1 : Mx D V.rank V.rank) i j) ∈ intAE D := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]; exact (by simpa using GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE (D := D) 1)
    · rw [map_zero]; exact zero_mem _
  let U : Subgroup (GA D V) :=
    { carrier := {k | (∀ i j, finPart D (mt V k i j) ∈ intAE D) ∧ ∀ i j, finPart D (mt V k⁻¹ i j) ∈ intAE D}
      one_mem' := by
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [show mt V 1 = 1 from rfl]; exact hone i j
        · rw [inv_one, show mt V 1 = 1 from rfl]; exact hone i j
      mul_mem' := by
        rintro k l ⟨hk, hk'⟩ ⟨hl, hl'⟩
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [show mt V (k * l) = mt V k * mt V l from rfl]; exact hint _ _ hk hl i j
        · rw [mul_inv_rev, show mt V (l⁻¹ * k⁻¹) = mt V l⁻¹ * mt V k⁻¹ from rfl]; exact hint _ _ hl' hk' i j
      inv_mem' := by
        rintro k ⟨hk, hk'⟩
        exact ⟨hk', by simpa using hk⟩ }
  refine ⟨U, ?_, fun k hk => hk.1⟩
  have hmt : Continuous (mt V) := GlobalTheory.MixModel.continuous_mt V
  have hmti : Continuous fun k : GA D V => mt V k⁻¹ := hmt.comp continuous_inv
  have hopen : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have h1 := GlobalTheory.CompanionTheory.Ipf.Bdd.isOpen_nsmul_mem (D := D) 1
    simp only [one_nsmul] at h1
    exact h1
  have e : (U : Set (GA D V)) = (⋂ i, ⋂ j, (fun k : GA D V => finPart D (mt V k i j)) ⁻¹' {z | z ∈ intAE D}) ∩
      ⋂ i, ⋂ j, (fun k : GA D V => finPart D (mt V k⁻¹ i j)) ⁻¹' {z | z ∈ intAE D} := by
    ext k; simp [U]
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact hopen.preimage (hfc.comp ((continuous_apply j).comp ((continuous_apply i).comp hmt)))
  · exact hopen.preimage (hfc.comp ((continuous_apply j).comp ((continuous_apply i).comp hmti)))

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBdd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {θ : InfFam D} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem bound_all {v : Pl D} (U : Subgroup (G D n)) (hUo : IsOpen (U : Set (G D n))) (Φ : schwartzA θ W.rank n)
    (hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Φ (γ * g) h = theta ω Φ g h)
    (hfix : ∀ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Φ = Φ)
    (hU : ∀ k k' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k' →
      k ∈ U → k' ∈ U)
    (hdec : ∀ g : G D n, ∃ γ ∈ GF D n, ∃ g' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g' = 1 ∧
      ∃ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} ∧ g = γ * g' * k)
    (hb : ∀ Q : Set (G D n), IsCompact Q → ∃ b : ℝ, ∀ g ∈ Q, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 →
      ∀ h, ‖theta ω Φ g h‖ ≤ b)
    (K₀ : Set (G D n)) (hK₀ : IsCompact K₀) : ∃ b : ℝ, ∀ g ∈ K₀, ∀ h, ‖theta ω Φ g h‖ ≤ b := by
  have hred : ∀ γ ∈ GF D n, ∀ g' k, k ∈ U → k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ h,
      theta ω Φ (γ * g' * k) h = theta ω Φ g' h := by
    intro γ hγ g' k hk hkv h
    rw [mul_assoc, hrat γ hγ]
    unfold theta
    rw [map_mul, Module.End.mul_apply, hfix k hk hkv]
  choose γf hγf g'f hg'f kf hkf hkvf hgf using hdec
  obtain ⟨W₀, hW₀c, hW₀1, hW₀U⟩ := exists_compact_subset hUo (one_mem U)
  have hW₀n : W₀ ∈ 𝓝 (1 : G D n) := mem_interior_iff_mem_nhds.1 hW₀1
  have hN : ∀ g₀ : G D n, {g | g₀⁻¹ * g ∈ W₀} ∈ 𝓝 g₀ := fun g₀ =>
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW₀n)
  obtain ⟨t, -, hcov⟩ := hK₀.elim_nhds_subcover (fun g₀ => {g | g₀⁻¹ * g ∈ W₀}) fun g₀ _ => hN g₀
  let τ : G D n → G D n := fun ε => ε * (locPart v ε)⁻¹
  have hτ : Continuous τ := continuous_id.mul ((continuous_locPart v).inv)
  let Q : Set (G D n) := ⋃ g₀ ∈ t, (fun ε => g'f g₀ * τ ε) '' W₀
  have hQ : IsCompact Q := t.isCompact_biUnion fun g₀ _ => hW₀c.image (continuous_const.mul hτ)
  obtain ⟨b, hb'⟩ := hb Q hQ
  refine ⟨b, fun g hg h => ?_⟩
  obtain ⟨g₀, hg₀t, hgg₀⟩ := Set.mem_iUnion₂.1 (hcov hg)
  set ε := g₀⁻¹ * g with hε
  have hεW : ε ∈ W₀ := hgg₀
  set εv := locPart v ε with hεv
  set ε' := τ ε with hε'
  have hpv : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ε' = 1 := by
    show GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v (ε * (locPart v ε)⁻¹) = 1
    rw [map_mul, map_inv, proj_locPart, mul_inv_cancel]
  have hc : kf g₀ * ε' = ε' * kf g₀ := commute_of_atPts (hkvf g₀) hpv
  have hsplit : ε' * εv = ε := by
    show ε * (locPart v ε)⁻¹ * locPart v ε = ε
    group
  have hkU : kf g₀ * εv ∈ U := mul_mem (hkf g₀) (hU ε εv (proj_locPart v ε).symm (hW₀U hεW))
  have hkv : kf g₀ * εv ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem (hkvf g₀) (locPart_mem_atPts v ε)
  have heq : g = γf g₀ * (g'f g₀ * ε') * (kf g₀ * εv) := by
    calc g = g₀ * ε := by rw [hε]; group
      _ = γf g₀ * g'f g₀ * kf g₀ * (ε' * εv) := by rw [← hgf g₀, hsplit]
      _ = γf g₀ * g'f g₀ * (kf g₀ * ε') * εv := by simp only [mul_assoc]
      _ = γf g₀ * g'f g₀ * (ε' * kf g₀) * εv := by rw [hc]
      _ = _ := by simp only [mul_assoc]
  rw [heq, hred _ (hγf g₀) _ _ hkU hkv]
  refine hb' _ (Set.mem_iUnion₂.2 ⟨g₀, hg₀t, ε, hεW, rfl⟩) ?_ h
  rw [map_mul, hg'f g₀, hpv, one_mul]

end PositivityTheory.Rg.Rsw.L.LThBdd

namespace PositivityTheory.Rg.Rsw.L

open LThBdd in
theorem thBdd : WMaj → LatBound → WeakApproximationFinitePlace → ThBdd := by
  intro hWM hLB hWA D n W ψ hψ χ hχ hη θ hθ μ hμ ω hω nb hnb v C hC Ψ Ψ' hΨ hΨ'
  obtain ⟨𝓕, hμ'⟩ := hμ
  have hW := hWM D n W ψ hψ χ hχ hη θ hθ μ ⟨𝓕, hμ'⟩ ω hω Ψ'
  have hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Ψ' (γ * g) h = theta ω Ψ' g h :=
    fun γ hγ g h => theta_rat hψ hχ hθ hμ' hω Ψ' hγ g h
  have hfix : ∀ k ∈ Ucut nb v C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Ψ' = Ψ' :=
    fun k hk hkv => fix_open hnb C Ψ Ψ' hΨ hΨ' hk hkv
  refine ⟨theta_cont hθ Ψ' hW.1 hW.2, hrat, ⟨Ucut nb v C.s, isOpen_Ucut _ _ _, hfix⟩, fun K₀ hK₀ => ?_,
    fun x g hg => ⟨omega_cut hω hnb C Ψ Ψ' hΨ' hg, theta_nb hω hnb C hC Ψ Ψ' hΨ hΨ' x hg⟩⟩
  exact bound_all (Ucut nb v C.s) (isOpen_Ucut _ _ _) Ψ' hrat hfix (fun k k' e hk => mem_Ucut_of_proj e hk)
    (fun g => hWA D n v (Ucut nb v C.s) (isOpen_Ucut _ _ _) g)
    (bound_triv hω hnb C hC Ψ Ψ' hΨ hΨ' hLB hθ hW.2) K₀ hK₀

end PositivityTheory.Rg.Rsw.L

end
end

