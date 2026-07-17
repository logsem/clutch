# Heterogenous Database

In this folder you can find the representation of the evolution of
$h$ on a database with a huge domain and the distribution over it
is far from beeing uniform.

## Evolution with the probability distribution (Hasthbl. implmentation)

With the following parameters :

|   Parameter   |    Value   |
|:--------------|-----------:|
| $\varepsilon$ |        $1$ |
| $\alpha$      |     $1/10$ |
| $\beta$       |     $1/10$ |
| $\eta$        | $\alpha/2$ |

We get the following evolution :

![Evolution of the distribution.](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/private_multiplicative_weights/gif/heterogenous_database/evolution_distrib.gif?raw=true "Evolution of the distribution.")

We don't have the issue in the normalizing step.

## Evolution with the count histograms (List. implementation)

With the following parameters :

|   Parameter   |    Value   |
|:--------------|-----------:|
| $\varepsilon$ |        $1$ |
| $\alpha$      |    $1/100$ |
| $\beta$       |    $1/100$ |
| $\eta$        | $\alpha$/2 |

We get the following evolution :

![Evolution of the distribution.](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/private_multiplicative_weights/gif/heterogenous_database/evolution_distrib_issue.gif?raw=true "Evolution of the distribution with overestimation of the first elements.")

We can see the issue in the scaling step.
The firsts elements are overestimated and
some elements (the small ones) are underestimated.

While with the following parameters :

|   Parameter   |    Value   |
|:--------------|-----------:|
| $\varepsilon$ |        $1$ |
| $\alpha$      |    $1/100$ |
| $\beta$       |    $1/100$ |
| $\eta$        | $6*\alpha$ |

We get the following evolution :

![Evolution of the distribution.](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/private_multiplicative_weights/gif/heterogenous_database/evolution_distrib_alf.gif?raw=true "Evolution of the distribution with an addapted learning factor.")
