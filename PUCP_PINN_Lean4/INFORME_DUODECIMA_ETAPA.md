# Duodécima etapa: tasa poblacional (3.26)

## Enunciado de la tesis y resultado Lean

El Teorema 3.8, bajo las Hipótesis 3.2 y 3.7, fija `0<α≤1`, pesos residuales `λr,λb>0`, los pesos de regularización iguales `a_m=max(λ̂Rr,m,λ̂Rb,m)` de (3.23), minimizadores globales mensurables y tamaños `mr=O(mb^(d/(d−1)))`. Para `d=2`, la conclusión (3.26) es `LossPINN(h_m;λ)=O(mr^(-α/2))` sobre el evento de cobertura, y la sucesión de tamaños satisface `mr(n),mb(n)≥n` eventualmente. La Hipótesis 3.7 exige comparadores mensurables que interpolen exactamente, con `R*(ω)<∞` uniformemente en los índices sobre un evento de probabilidad uno.

`tasa_poblacional_eventual_casi_segura` formaliza esa conclusión en la notación `IsBigO` de Mathlib y da además una constante explícita: para casi todo `ω`, existe `C(ω)≥0` tal que, eventualmente, `0≤Loss_n(ω)≤C(ω) mr(n)^(-α/2)`. Con una constante `K>0` en `mr(n)≤K mb(n)^2`, se puede tomar

`C(ω)=3[λr(√2 cr^(-1/2))^(2α)+λb(√2 cb^(-1))^(2α)K^(α/2)] [R*(ω)+Sf²+Sg²]`.

El teorema usa `problemaMuestral`, cuya definición sustituye los puntos empíricos por los prefijos exactos de dos sucesiones i.i.d. sobre un mismo espacio de probabilidad. La cobertura simultánea proviene de `coberturas_cuadrado_eventuales_casi_seguras`. La concentración de las medidas da pertenencia casi segura de **todas** las muestras a `U` y `Γ`; no se exige como hipótesis independiente. El radio final `√2η`, y no solo `η`, entra eventualmente en `(0,ε₀]`. La integrabilidad poblacional se deriva de cotas Hölder en soportes acotados y de continuidad de los residuos sobre sus soportes.

La identidad algebraica comprobada es `C_m a_m=3 max(λr εr^(2α),λb εb^(2α))`, con prueba de `C_m>0`. En la escala del Lema 3.6, `εr^(2α)=Ar mr^(-α/2)` y `εb^(2α)=Ab mb^(-α)` con `Ar=(√2 cr^(-1/2))^(2α)` y `Ab=(√2 cb^(-1))^(2α)`. De `mr≤K mb²` resulta `mb^(-α)≤K^(α/2) mr^(-α/2)`, sin identificar los dos tamaños ni introducir logaritmos.

## Hipótesis visibles y diferencias con el texto literal

- Las particiones, cotas de masa, leyes i.i.d. y concentración se suministran como datos, tal como en la Hipótesis 3.2. El teorema abstrae el espacio interior y el de frontera como espacios pseudométricos; codifica la dimensión dos mediante exponentes de masa `2` y `1` y radio geométrico `√2η`. No prueba aquí la regularidad `C^{0,1}` de un dominio concreto, la inclusión `Γ⊆∂U`, la absoluta continuidad o las cotas inferiores esenciales de densidad: estas últimas no intervienen en (3.26). Tampoco usa independencia entre las dos secuencias, innecesaria para intersectar dos eventos de probabilidad uno.
- `Hm(n)`, `hm(n,ω)` y `g(n,ω)` representan la clase, el minimizador y el comparador. Se presupone selección mensurable de ambos; la existencia de minimizadores no se deduce de la arquitectura. El evento `hstats` codifica minimalidad, interpolación exacta y `R*(ω)<∞` eventualmente. La tesis las exige simultáneamente para todos los índices sobre su evento, condición más fuerte.
- `CotasHolder` fija las seminormas que realmente controlan los incrementos de operadores y datos. Se pide también la continuidad sobre los soportes de `L[hm]`, `B[hm]`, `f` y `g`, correspondiente a la regularidad `C^{0,α}` de la Hipótesis 3.7. La prueba de integrabilidad usa esa continuidad para obtener mensurabilidad espacial casi en todas partes.
- La familia base conserva las medidas y los pesos residuales entre índices y fija los pesos de regularización exactamente según (3.23). Son igualdades visibles porque `ProblemaPINN` es un registro abstracto. La cota `mr≤K mb²` se da en su forma eventual explícita, equivalente a la relación `O(mb²)` de la tesis para tamaños positivos.
- Se exige que los soportes `U` y `Γ` sean acotados, como en la Hipótesis 3.2. Su no vacuidad se deduce en Lean de la concentración de medidas de probabilidad. El teorema usa solo `0<α` en los cálculos, pero mantiene la premisa `α≤1` del texto.

El resultado central está formulado con `∀ᵐ ω`, que es la noción de casi en todas partes de Mathlib. `measurableSet_eventual_cota_poblacional` y `prob_uno_eventual_cota_poblacional` prueban que el **evento de tasa** es medible y tiene probabilidad uno si cada función aleatoria `ω↦Loss_n(ω)` es medible. La mensurabilidad de `hm(n,·)` y `g(n,·)` está representada, pero por sí sola no implica la mensurabilidad de la pérdida: el registro abstracto no especifica measurabilidad conjunta en candidato y muestra de `L`, `B` y las operaciones de integración. Esta condición de composición queda identificada como puente pendiente para afirmar la igualdad de medida uno del evento concreto sin una hipótesis adicional.

## Estado lógico

La implicación (3.26) **está probada** en Lean bajo la representación explícita de las Hipótesis 3.2 y 3.7 anterior, con una conclusión `IsBigO` eventual casi segura. No se construyen comparadores, minimizadores ni clases neuronales para un problema particular. La mensurabilidad del evento concreto de tasa tiene un lema condicional separado. Las convergencias uniformes (3.27) y tasas uniformes (3.28) permanecen pendientes; el Teorema 3.8 completo no se declara formalizado.

## Verificación

Lean `v4.35.0`, Mathlib `v4.35.0`, EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. No se modificaron la tesis ni las pruebas Lean anteriores. El módulo nuevo no contiene `sorry`, `admit` ni axiomas nuevos. Las consultas `#print axioms` de los teoremas nuevos muestran únicamente `propext`, `Classical.choice` y `Quot.sound`.

`lake build` local terminó correctamente: **3224 trabajos**. El resultado del CI de la PR de esta etapa se añadirá tras su ejecución.
