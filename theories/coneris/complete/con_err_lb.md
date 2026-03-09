$f_\phi(\rho) := \sup_{\zeta,\Xi}(\Pr_{exec_\zeta(\Xi, \rho)}[\neg \phi] + 1 - \Pr_{pexec_\zeta(\Xi, \rho)}[True])$

$f_\phi(\rho) \ge \sup_{i} \mathbb{E}_{\rho' \sim tpStep(\rho,i)}[f_\phi(\rho')]$ when every thread of $\rho$ is reducible.

## Proof:

$$V_\zeta(\Xi, \rho) := \Pr_{exec_\zeta(\Xi, \rho)}[\neg \phi] + 1 - \Pr_{pexec_\zeta(\Xi, \rho)}[True]$$



$$f_\phi(\rho) = \sup_{\zeta, \Xi} V_\zeta(\Xi, \rho)$$

Since $\rho$ is not a final configuration:

* $exec_\zeta(\Xi, \rho) = schStep_\zeta(\Xi, \rho) \gg= exec_\zeta$
* $pexec_\zeta(\Xi, \rho) = schStep_\zeta(\Xi, \rho) \gg= pexec_\zeta$

We can rewrite $V_\zeta$ recursively over the first scheduler step:

$$V_\zeta(\Xi, \rho) = \mathbb{E}_{(\Xi', \rho') \sim schStep_\zeta(\Xi, \rho)} [ V_\zeta(\Xi', \rho') ]$$

Let $\epsilon > 0$. We will construct a specific composite scheduler to show we can get arbitrarily close to the supremum.

1. Pick a thread $i^*$ such that $\mathbb{E}_{\rho' \sim tpStep(\rho, i^*)}[f_\phi(\rho')] = \sup_i \mathbb{E}_{\rho' \sim tpStep(\rho, i)}[f_\phi(\rho')]$.
2. For every possible next state $\rho'$, the definition of $f_\phi(\rho')$ guarantees there exists some scheduler $\zeta_{\rho'}$ and initial state $\Xi_{\rho'}$ such that $V_{\zeta_{\rho'}}(\Xi_{\rho'}, \rho') \geq f_\phi(\rho') - {\epsilon}$.

We construct a new scheduler $\zeta^*$ and special initial state $\Xi^*$ that behaves as follows:
At $(\Xi^*, \rho)$, $\zeta^*$ deterministically chooses the thread index $i^*$. Once $tpStep$ transitions the program to configuration $\rho'$, the scheduler sets its internal state to $\Xi_{\rho'}$ and subsequently behaves exactly like $\zeta_{\rho'}$ for the remainder of execution.

Evaluating $V$ under our constructed $\zeta^*$:


$$V_{\zeta^*}(\Xi^*, \rho) = \sum_{\rho'} tpStep(\rho, i^*)(\rho') V_{\zeta_{\rho'}}(\Xi_{\rho'}, \rho')$$

Substitute the bound for $V_{\zeta_{\rho'}}$:


$$V_{\zeta^*}(\Xi^*, \rho) \geq \sum_{\rho'} tpStep(\rho, i^*)(\rho') \left( f_\phi(\rho') - {\epsilon} \right)$$

$$V_{\zeta^*}(\Xi^*, \rho) \geq \mathbb{E}_{\rho' \sim tpStep(\rho, i^*)}[f_\phi(\rho')] - {\epsilon}$$

Substitute the bound for $i^*$:

$$V_{\zeta^*}(\Xi^*, \rho) \geq \sup_i \mathbb{E}_{\rho' \sim tpStep(\rho, i)}[f_\phi(\rho')] - \epsilon$$

Since $f_\phi(\rho)$ is the absolute supremum over *all* possible schedulers and states, it must be that $f_\phi(\rho) \geq V_{\zeta^*}(\Xi^*, \rho)$. Therefore:


$$f_\phi(\rho) \geq \sup_i \mathbb{E}_{\rho' \sim tpStep(\rho, i)}[f_\phi(\rho')] - \epsilon$$

Because this holds for any $\epsilon > 0$, 
$$f_\phi(\rho) \geq \sup_i \mathbb{E}_{\rho' \sim tpStep(\rho, i)}[f_\phi(\rho')]$$

$\square$