import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsBeta
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.RinfZero
section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem absMax {Q Q' P ι : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup P] [Module ℂ P]
    {p : Q →ₗ[ℂ] P} {p' : Q' →ₗ[ℂ] P} {S : Submodule ℂ Q} {S' : Submodule ℂ Q'} {R : ι → Q → Q → Prop} {R' : ι → Q' → Q' → Prop}
    (on : S.map p = ⊤) (on' : S'.map p' = ⊤) (ex : ∀ i, ∀ x ∈ S, ∃ y, R i x y) (ex' : ∀ i, ∀ x ∈ S', ∃ y, R' i x y)
    (z : ∀ i, R i 0 0) (z' : ∀ i, R' i 0 0)
    (eqv : ∀ i, ∀ x ∈ S, ∀ x' ∈ S', ∀ y y', R i x y → R' i x' y' → p x = p' x' → p y = p' y')
    (irr : ∀ N : Submodule ℂ P, (∀ i, ∀ x ∈ S, ∀ y, R i x y → p x ∈ N → p y ∈ N) → N = ⊥ ∨ N = ⊤) :
    ((∀ i, ∀ x ∈ S, ∀ y, R i x y → p x = 0 → p y = 0) ∧
      ∀ N ≤ S, (∀ i, ∀ x ∈ N, ∀ y, R i x y → y ∈ N) → N.map p = ⊥ ∨ N.map p = ⊤) ∧
    (∀ i, ∀ x ∈ S', ∀ y, R' i x y → p' x = 0 → p' y = 0) ∧
      ∀ N ≤ S', (∀ i, ∀ x ∈ N, ∀ y, R' i x y → y ∈ N) → N.map p' = ⊥ ∨ N.map p' = ⊤ := by
  refine ⟨⟨fun i x hx y h h0 => by simpa using eqv i x hx 0 S'.zero_mem y 0 h (z' i) (by simpa using h0), fun N hN hs => irr _ ?_⟩,
    fun i x hx y h h0 => by simpa using (eqv i 0 S.zero_mem x hx 0 y (z i) h (by simpa using h0.symm)).symm,
    fun N hN hs => irr _ ?_⟩
  · rintro i x hx y h ⟨w, hw, e⟩
    obtain ⟨x', hx', e'⟩ : p x ∈ S'.map p' := on' ▸ Submodule.mem_top
    obtain ⟨y', hy'⟩ := ex' i x' hx'
    obtain ⟨w₁, hw₁⟩ := ex i w (hN hw)
    exact ⟨w₁, hs i w hw w₁ hw₁,
      (eqv i w (hN hw) x' hx' w₁ y' hw₁ hy' (e.trans e'.symm)).trans (eqv i x hx x' hx' y y' h hy' e'.symm).symm⟩
  · rintro i x hx y h ⟨w, hw, e⟩
    obtain ⟨w₁, hw₁⟩ := ex' i w (hN hw)
    exact ⟨w₁, hs i w hw w₁ hw₁, (eqv i x hx w (hN hw) y w₁ h hw₁ e.symm).symm⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem acts_zero {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R) (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts ev T 0 0 :=
  fun r _ => by
    have : tens ev 0 r = 0 := funext fun x => by simp [tens]
    rw [this, map_zero]

theorem actsD_zero {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R) (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD ev (fun t => T t) 0 0 := fun r _ x => by
  have : tens ev 0 r = 0 := funext fun x => by simp [tens]
  simp only [this, map_zero]
  exact hasDerivAt_const _ _

theorem augAt_le (v : Pl F) : augAt om v ≤ SB _ := Submodule.span_le.2 (by
  rintro _ ⟨g, -, x, hx, y, hy, -, rfl⟩
  exact sub_mem hy hx)

theorem one_at' {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev :=
  fun u _ => by simp [mat]

theorem ex_fin (hp : IsPair B M χX χW om r s r' s') (v : Pl F) (h : UAt σ W (evFin F v)) :
    ∀ x ∈ SB (Fin n × Fin d → Fv F v), ∃ y, y ∈ SB _ ∧ Acts (evFin F v) (om (1, h.1)) x y := fun x hx => by
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ n d B X W M om
    ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, ⟨_, _, hp.weil⟩⟩ v
  exact ⟨_, hω.pres 1 (one_at' _) h h.2 x hx, (hω.acts 1 (one_at' _) h h.2 x hx _).2 rfl⟩

def RInf (B : Base F E) (om : Rep σ X W) : Lines σ W ⊕ KInf σ W B.emb → SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d) → Prop
  | .inl γ, f, g => ActsD (evI F) (fun t => om (1, γ.1 (Multiplicative.ofAdd t))) f g
  | .inr k, f, g => Acts (evI F) (om (1, k.1)) f g

theorem kinf_one {m : ℕ} {Y : Spc F E m} (τ) : (1 : UA σ Y.J) ∈ KInf σ Y τ :=
  ⟨one_at' _, fun w => by
    have : (mat (1 : UA σ Y.J)).map (piInf (τ w)) = 1 := by simp [mat]
    rw [this]; exact Commute.one_left _⟩

theorem pol_lie (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {γ δ} (hγ : γ ∈ Lines σ X)
    (hδ : δ ∈ Lines σ W) {f} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ g ∈ M.Pol B.ψ B.emb, ∀ g' : SInf F _,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))) f g' ↔ g' = g := by
  choose op hop _ using hO F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨g, h1, h2, -⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ δ hδ (fun t => op _ (hγ.2 _) _ (hδ.2 _))
    (fun t => hop _ _ _ _) f hf
  exact ⟨g, h1, fun g' => ⟨fun h => (hQ F _ f g' g).2 _ h h2, fun h => h ▸ h2⟩⟩

theorem pol_k (hO : ArchOp) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {k k'} (hk : k ∈ KInf σ X B.emb)
    (hk' : k' ∈ KInf σ W B.emb) {f} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ g ∈ M.Pol B.ψ B.emb, ∀ g' : SInf F _, Acts (evI F) (om (k, k')) f g' ↔ g' = g := by
  obtain ⟨T, h1, h2⟩ := hO F E σ B n d X W M χX χW om r s r' s' hp k hk.1 k' hk'.1
  exact ⟨T f, h2 hk hk' f hf, fun g' => ⟨fun h => (hQ F _ f g' _).1 _ h (h1.2 f), fun h => h ▸ h1.2 f⟩⟩

theorem rinf_ex (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') (i) {f}
    (hf : f ∈ M.Pol B.ψ B.emb) : ∃ g ∈ M.Pol B.ψ B.emb, ∀ g', RInf B om i f g' ↔ g' = g := by
  rcases i with γ | k
  · exact pol_lie hO hL hQ hp (γ := 1) ⟨continuous_const, fun _ => one_at' _⟩ γ.2 hf
  · exact pol_k hO hQ hp (kinf_one _) k.2 hf

theorem rinf_zero (i) : RInf B om i 0 0 := by
  rcases i with γ | k
  · exact actsD_zero _ fun t => om (1, γ.1 (Multiplicative.ofAdd t))
  · exact acts_zero _ _

theorem max_fin {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P] {v : Pl F} {p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P}
    (on : (SB _).map p = ⊤) (inv : augAt om v ≤ LinearMap.ker p)
    (h : (∀ i : UAt σ W (evFin F v), ∀ x ∈ SB _, ∀ y, y ∈ SB _ ∧ Acts (evFin F v) (om (1, i.1)) x y → p x = 0 → p y = 0) ∧
      ∀ N ≤ SB _, (∀ i : UAt σ W (evFin F v), ∀ x ∈ N, ∀ y, y ∈ SB _ ∧ Acts (evFin F v) (om (1, i.1)) x y → y ∈ N) →
        N.map p = ⊥ ∨ N.map p = ⊤) :
    Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker p ⊓ SB _) :=
  maximal_of p _ _ on (fun _ h => h.2.1)
    ⟨le_inf inv (augAt_le v), inf_le_right, fun g hg x hx y hy e => ⟨h.1 ⟨g, hg⟩ x hx.2 y ⟨hy, e⟩ hx.1, hy⟩⟩
    fun N hN => h.2 N hN.2.1 fun i x hx y hy => hN.2.2 i i.2 x hx y hy.1 hy.2

theorem max_inf (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {P : Type} [AddCommGroup P]
    [Module ℂ P] [Nontrivial P] {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (q : RealQuot B M om p)
    (h : (∀ i, ∀ x ∈ M.Pol B.ψ B.emb, ∀ y, RInf B om i x y → p x = 0 → p y = 0) ∧
      ∀ N ≤ M.Pol B.ψ B.emb, (∀ i, ∀ x ∈ N, ∀ y, RInf B om i x y → y ∈ N) → N.map p = ⊥ ∨ N.map p = ⊤) :
    Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P ∧ P ≠ M.Pol B.ψ B.emb) (LinearMap.ker p ⊓ M.Pol B.ψ B.emb) := by
  have st : ∀ i, ∀ x ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb, ∀ y, RInf B om i x y → y ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb :=
    fun i x hx y hy => by
      obtain ⟨g, hg, e⟩ := rinf_ex hO hL hQ hp i hx.2
      exact ⟨h.1 i x hx.2 y hy hx.1, (e y).1 hy ▸ hg⟩
  refine maximal_of p _ _ q.onto (fun _ h => h.1) ⟨inf_le_right, fun γ hγ f hf y hy => ⟨q.lie γ hγ f hf y hy, ?_⟩,
    fun k hk f hf y hy => ⟨show p (y - f) = 0 by rw [map_sub, q.cpt k hk f hf y hy, sub_self], ?_⟩,
    fun γ hγ f hf y hy => st (.inl ⟨γ, hγ⟩) f hf y hy, fun k hk f hf y hy => st (.inr ⟨k, hk⟩) f hf y hy⟩
    fun N hN => h.2 N hN.1 ?_
  · obtain ⟨g, hg, e⟩ := pol_lie hO hL hQ hp hγ (δ := 1) ⟨continuous_const, fun _ => one_at' _⟩ hf
    exact (e y).1 hy ▸ hg
  · obtain ⟨g, hg, e⟩ := pol_k hO hQ hp hk (kinf_one _) hf
    exact sub_mem ((e y).1 hy ▸ hg) hf
  · rintro (γ | k) x hx y hy
    exacts [hN.2.2.2.1 γ γ.2 x hx y hy, hN.2.2.2.2 k k.2 x hx y hy]

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem maxFinP (m : IsMatched B G X om om' R Rf) (v : Pl F) :
    Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf.p v) ⊓ SB _) ∧
      Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf.p' v) ⊓ SB _) := by
  haveI := m.fin.nontriv v
  have := absMax (R := fun (i : UAt σ G.W (evFin F v)) x y => y ∈ SB _ ∧ Acts (evFin F v) (om (1, i.1)) x y)
    (R' := fun (i : UAt σ G.W (evFin F v)) x y => y ∈ SB _ ∧ Acts (evFin F v) (om' (1, i.1)) x y) (m.fin.onto v) (m.fin.onto' v)
    (ex_fin (PositivityTheory.ThKG.pairV m.triple) v) (ex_fin (PositivityTheory.ThKG.pairV' m.triple) v)
    (fun _ => ⟨zero_mem _, acts_zero _ _⟩) (fun _ => ⟨zero_mem _, acts_zero _ _⟩)
    (fun i x hx x' hx' y y' h h' => m.fin.equiv v i i.2 x hx x' hx' y h.1 y' h'.1 h.2 h'.2)
    fun N hN => m.fin.irred v N fun h hh x hx y hy e => hN ⟨h, hh⟩ x hx y ⟨hy, e⟩
  exact ⟨max_fin (m.fin.onto v) (m.fin.inv v) this.1, max_fin (m.fin.onto' v) (m.fin.inv' v) this.2⟩

theorem maxInfP (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (m : IsMatched B G X om om' R Rf) :
    Maximal (fun P => GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om P ∧ P ≠ G.M.Pol B.ψ B.emb)
        (LinearMap.ker R.p ⊓ G.M.Pol B.ψ B.emb) ∧
      Maximal (fun P => GlobalTheory.Published.ThetaSubInf G.M' B.ψ B.emb om' P ∧ P ≠ G.M'.Pol B.ψ B.emb)
        (LinearMap.ker R.p' ⊓ G.M'.Pol B.ψ B.emb) := by
  haveI := m.real.nontriv
  have p1 := PositivityTheory.ThKG.pairV m.triple
  have p2 := PositivityTheory.ThKG.pairV' m.triple
  have := absMax (R := RInf B om) (R' := RInf B om') m.real.quot.onto m.real.quot'.onto
    (fun i x hx => let ⟨g, _, e⟩ := rinf_ex hO hL hQ p1 i hx; ⟨g, (e g).2 rfl⟩)
    (fun i x hx => let ⟨g, _, e⟩ := rinf_ex hO hL hQ p2 i hx; ⟨g, (e g).2 rfl⟩) rinf_zero rinf_zero
    (by
      rintro (γ | k) x hx x' hx' y y' h h'
      exacts [m.real.lie γ γ.2 x hx x' hx' y y' h h', m.real.cpt k k.2 x hx x' hx' y y' h h'])
    fun N hN => m.real.irred N (fun γ hγ => hN (.inl ⟨γ, hγ⟩)) fun k hk => hN (.inr ⟨k, hk⟩)
  exact ⟨max_inf hO hL hQ p1 m.real.quot this.1, max_inf hO hL hQ p2 m.real.quot' this.2⟩

end PositivityTheory.ThKF

end
end

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.UpdSelf
section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

def upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x : (κ → Fv F v) → ℂ) : ∀ u : Pl F, (κ → Fv F u) → ℂ := by
  classical exact Function.update φ v x

theorem upd_self {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) : upd φ v x v = x := by
  classical exact Function.update_self ..

theorem upd_ne {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) {u} (h : u ≠ v) : upd φ v x u = φ u := by
  classical exact Function.update_of_ne h ..

theorem upd_eq {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) : upd φ v (φ v) = φ := by
  classical exact Function.update_eq_self ..

theorem upd_upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x y) : upd (upd φ v x) v y = upd φ v y := by
  classical exact Function.update_idem ..

theorem upd_sb {κ : Type} [Fintype κ] {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {v : Pl F} {x} (hx : x ∈ SB _) (u) :
    upd φ v x u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [upd_self]
  · rw [upd_ne _ _ _ e]; exact h u

theorem upd_cof {κ : Type} {φ ψ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = ψ u) (v : Pl F) (x) :
    ∀ᶠ u in cofinite, upd φ v x u = ψ u :=
  (h.and (Filter.eventually_cofinite_ne v)).mono fun _ hu => (upd_ne _ _ _ hu.2).trans hu.1

theorem intersection_update_fsHerm_neg_one (hP : PureAct) (hp : IsPair B M χX χW om r s r' s') (f : SInf F (Fin n × Fin d)) {φ} (h1 : ∀ u, φ u ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = M.vac u) (v : Pl F) :
    ∃ j : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d, (∀ x, j x = pure f (upd φ v x)) ∧
      ∀ S, ∀ x ∈ SB _, ∀ y, Acts (evFin F v) S x y → S (j x) = j y := by
  have h3 := (h2.and hp.good.std).mono fun _ h => h.1.trans h.2
  have l : ∀ x y (a : ℂ), pure f (upd φ v (x + a • y)) = pure f (upd φ v x) + a • pure f (upd φ v y) :=
    (hP F _ v id f φ h1 h3).2.1
  have z : pure f (upd φ v 0) = 0 := by
    have := l 0 0 1
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨{ toFun := fun x => pure f (upd φ v x)
            map_add' := fun x y => by simpa using l x y 1
            map_smul' := fun c x => by
              have := l 0 x c
              rwa [zero_add, z, zero_add] at this },
    fun _ => rfl, fun S x hx y hxy => ?_⟩
  have := (hP F _ v S f (upd φ v x) (upd_sb h1 hx) (upd_cof h3 v x)).2.2 y (by rwa [upd_self])
  exact this.trans (congrArg (pure f) (upd_upd φ v x y))

theorem killFin (hU : Unimod) (hT : ThetaBasic) (hP : PureAct) (hL : LocCpt) (hp : IsPair B M χX χW om r s r' s') {𝓒}
    (hc : Cls B M om 𝓒) (v : Pl F) (adm : AdmAt om v) {N}
    (hN : Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N)
    (hu : ∀ N', Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N' → N' = N)
    {f} (hf : f ∈ M.Pol B.ψ B.emb) {φ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u)
    (h𝓒 : ∀ x ∈ SB _, pure f (upd φ v x) ∈ 𝓒) (hv : φ v ∈ N) : M.I om (pure f φ) = 0 := by
  classical
  obtain ⟨j, hj, hjS⟩ := intersection_update_fsHerm_neg_one hP hp f h1 h2 v
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ n d B X W M om
    ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, ⟨_, _, hp.weil⟩⟩ v
  obtain ⟨hΓ, μ, 𝓕, hμ, h𝓕, hr⟩ := uniW hU hp
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  obtain ⟨hinv, hmul, hcpt⟩ := hL F E σ d W v
  have o1 : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by simp [mat]
  have o2 : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by simp [mat]
  let Q := SB (Fin n × Fin d → Fv F v)
  have jc : ∀ x : Q, j x ∈ 𝓒 := fun x => hj x ▸ h𝓒 x x.2
  let u : Q →ₗ[ℂ] (UA σ W.J → ℂ) :=
    { toFun := fun x => M.I om (j x)
      map_add' := fun x y => by rw [Submodule.coe_add, map_add, I_add' hp hc (jc x) (jc y)]
      map_smul' := fun c x => funext fun h => by
        rw [Submodule.coe_smul, map_smul]; exact PositivityTheory.ThKG.I_smul M om c _ h }
  have hu' : ∀ x, u x = M.I om (j x) := fun _ => rfl
  have uc : ∀ x, Continuous (u x) := fun x => hc.cont _ (jc x)
  have u2 : ∀ x, IntegrableOn (fun g => ‖u x g‖ ^ 2) 𝓕 μ := fun x => hc.sq μ 𝓕 hμ h𝓕 _ (jc x)
    (hj x ▸ Submodule.subset_span ⟨f, hf, _, upd_sb h1 x.2, upd_cof h2 v x, rfl⟩)
  have ui : ∀ x, L2.Inv (ratU σ W.J) (u x) := fun x => I_inv hT hp (hc.sch (jc x))
  obtain ⟨β, hβ, hs, hpos⟩ := exists_beta 𝓕 μ u uc u2
  let A : ∀ h ∈ UAt σ W (evFin F v), Module.End ℂ Q := fun h hh => (ω (1, h)).restrict (hω.pres 1 o1 h hh)
  have hA : ∀ h hh (x : Q), (A h hh x : _ → ℂ) = ω (1, h) x := fun _ _ _ => rfl
  have uA : ∀ h hh x g, u (A h hh x) g = u x (g * h) := fun h hh x g => by
    rw [hu', hu', hA h hh, ← hjS (om (1, h)) x x.2 _ ((hω.acts 1 o1 h hh x x.2 _).2 rfl), I_right]
  have iso : ∀ h hh x y, β (A h hh x) (A h hh y) = β x y := fun h hh x y => by
    simp only [hβ, uA]; exact L2.form_right h𝓕 (ui x) (ui y) h
  have Amul : ∀ h hh h' hh' x, A (h * h') (hmul h hh h' hh') x = A h hh (A h' hh' x) := fun h hh h' hh' x =>
    Subtype.ext (by
      have := hω.mul 1 o1 h hh 1 o1 h' hh' x x.2
      rw [mul_one] at this
      exact this)
  have Aone : ∀ x, A 1 o2 x = x := fun x => Subtype.ext (hω.one x x.2)
  let 𝒪 : Set (Module.End ℂ Q) := {T | ∃ h hh, T = A h hh}
  let A₀ : Submodule ℂ Q := (augAt om v).comap Q.subtype
  have augle : augAt om v ≤ Q := hN.prop.1.1.trans hN.prop.1.2.1
  have uaug : ∀ z ∈ augAt om v, M.I om (j z) = 0 := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨g, hg, x, hx, y, hy, hxy, rfl⟩ := h
      have e : j y = j (y - x) + j x := by rw [← map_add, sub_add_cancel]
      have e2 := I_add' hp hc (jc ⟨y - x, sub_mem hy hx⟩) (jc ⟨x, hx⟩)
      rw [← e, ← hjS _ x hx y hxy, I_left hU hT hp (hc.sch (jc ⟨x, hx⟩))] at e2
      exact (left_eq_add.1 (e2.trans (add_comm _ _)))
    | zero => rw [map_zero]; exact PositivityTheory.ThKG.I_zero M om
    | add a b ha hb iha ihb => rw [map_add, I_add' hp hc (jc ⟨a, augle ha⟩) (jc ⟨b, augle hb⟩), iha, ihb, add_zero]
    | smul c a _ iha => funext h; rw [map_smul, PositivityTheory.ThKG.I_smul, iha]; simp
  obtain ⟨m1, m2⟩ := max_comap Q (GlobalTheory.Published.ThetaSub om v) (fun P => A₀ ≤ P ∧ ∀ T ∈ 𝒪, ∀ x ∈ P, T x ∈ P)
    (fun _ h => h.2.1) (fun P => ⟨fun h => ⟨fun z hz => ⟨⟨z, augle hz⟩, h.1 hz, rfl⟩, Submodule.map_subtype_le _ _,
      by
        rintro g hg _ ⟨x, hx, rfl⟩ y - hxy
        exact ⟨A g hg x, h.2 _ ⟨g, hg, rfl⟩ x hx, ((hω.acts 1 o1 g hg x x.2 y).1 hxy).symm⟩⟩,
      fun h => ⟨fun x hx => by
          obtain ⟨y, hy, e⟩ := h.1 hx
          rwa [← show y = x from Subtype.ext e], by
        rintro _ ⟨g, hg, rfl⟩ x hx
        obtain ⟨y, hy, e⟩ := h.2.2 g hg x ⟨x, hx, rfl⟩ _ (A g hg x).2 ((hω.acts 1 o1 g hg x x.2 _).2 rfl)
        rwa [← show y = A g hg x from Subtype.ext e]⟩⟩) N hN hu
  have key := absUnit Q β 𝒪 A₀ hs hpos (fun x hx => by rw [hβ, hu', uaug x hx]; simp)
    (by
      rintro _ ⟨h, hh, rfl⟩
      refine ⟨_, ⟨h⁻¹, hinv h hh, rfl⟩, 1, fun x y => ?_⟩
      rw [one_mul, ← iso h hh x, ← Amul h hh h⁻¹ (hinv h hh)]
      simp only [mul_inv_cancel, Aone])
    (fun x₀ => by
      obtain ⟨U, hU1, hUf⟩ := hω.smooth x₀ x₀.2
      obtain ⟨K, hK, hKU, U', hU', hU'K⟩ := hcpt U hU1
      have kk : ∀ k : K, k.1 ∈ UAt σ W (evFin F v) := fun k => (hKU k.2).2
      let κ : K →* Module.End ℂ Q :=
        { toFun := fun k => A k (kk k)
          map_one' := LinearMap.ext Aone
          map_mul' := fun k k' => LinearMap.ext fun x => Amul k (kk k) k' (kk k') x }
      refine ⟨K, inferInstance, κ, fun k => ⟨k, kk k, rfl⟩, fun k => iso k (kk k), fun x => ?_, fun m ρ' hρ => ?_⟩
      · obtain ⟨V, hV1, hVf⟩ := hω.smooth x x.2
        obtain ⟨t, ht, hcov⟩ := hK.elim_nhds_subcover (fun g => (fun y => g⁻¹ * y) ⁻¹' V) fun g _ =>
          (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by
            show V ∈ 𝓝 (g⁻¹ * g)
            rwa [inv_mul_cancel])
        refine ⟨t.attach.image fun g => κ ⟨g.1, ht g.1 g.2⟩ x, fun k => Submodule.mem_sup_left (Submodule.subset_span ?_)⟩
        obtain ⟨g, hg, hk⟩ := Set.mem_iUnion₂.1 (hcov k.2)
        refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨g, hg⟩, Finset.mem_attach _ _, ?_⟩)
        have e : k = ⟨g, ht g hg⟩ * ((⟨g, ht g hg⟩ : K)⁻¹ * k) := by simp
        have e2 : κ ((⟨g, ht g hg⟩ : K)⁻¹ * k) x = x := Subtype.ext (hVf _ hk (kk _))
        conv_rhs => rw [e, map_mul, Module.End.mul_apply, e2]
      · have h1' := hρ fun k => Subtype.ext (hUf k (hKU k.2).1 (kk k))
        obtain ⟨t, ht⟩ := adm U' hU'
        refine ⟨(Finset.univ ×ˢ t).image fun p : Fin m × _ => LinearMap.single ℂ (fun _ => ℂ) p.1 ∘ₗ p.2 ∘ₗ Q.subtype,
          fun L hL hLe => ?_⟩
        have : L = ∑ i, LinearMap.single ℂ (fun _ => ℂ) i ∘ₗ (LinearMap.proj i ∘ₗ L) := by
          ext x i; simp [Pi.single_apply, Finset.sum_apply]
        rw [this]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨l, hl⟩ := LinearMap.exists_extend (LinearMap.proj i ∘ₗ L : Q →ₗ[ℂ] ℂ)
        have hl' : ∀ x : Q, l x = L x i := fun x => LinearMap.congr_fun hl x
        obtain ⟨l', hl't, hll⟩ := ht l (fun z hz => by
            rw [LinearMap.mem_ker, hl' ⟨z, augle hz⟩, show L ⟨z, augle hz⟩ = 0 from hL hz]; rfl)
          fun h hh hh' x hx y hy hxy => by
            have := hLe ⟨h, hU'K ⟨hh, hh'⟩⟩ ⟨x, hx⟩
            rw [h1', Module.End.one_apply] at this
            rw [hl' ⟨x, hx⟩, hl' ⟨y, hy⟩, ← this]
            exact congrFun (congrArg L (Subtype.ext ((hω.acts 1 o1 h hh' x hx y).1 hxy))) i
        have e : (LinearMap.proj i ∘ₗ L : Q →ₗ[ℂ] ℂ) = l' ∘ₗ Q.subtype := LinearMap.ext fun x => (hl' x).symm.trans (hll x x.2)
        rw [e]
        clear e hll
        induction hl't using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, y), by simpa using hy, rfl⟩))
        | zero => simp
        | add a b _ _ ha hb => rw [LinearMap.add_comp, LinearMap.comp_add]; exact add_mem ha hb
        | smul c a _ ha => rw [LinearMap.smul_comp, LinearMap.comp_smul]; exact Submodule.smul_mem _ _ ha)
    _ m1 m2 ⟨φ v, h1 v⟩ hv
  have := L2.eq_zero h𝓕 (uc _) (ui _) (u2 _) ((hβ _ _).symm.trans key)
  rwa [hu', hj, upd_eq] at this

end PositivityTheory.ThKF

end
end

