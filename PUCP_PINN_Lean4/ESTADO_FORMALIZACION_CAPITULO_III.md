# Estado verificable de la formalización del capítulo III

## Estado actual · etapa 28

La base es la [PR #29](https://github.com/MichaelMobius/tesispucp/pull/29), commit `09a0852e926392bc0f8146ca0105624c9cb486db`. El [informe de la etapa 28](INFORME_ETAPA28.md) registra el alcance del operador y la correspondencia con C3.23.

| Resultado | Declaración y alcance |
|---|---|
| Traza de Sobolev | `trazaSobolevCuadrado` es lineal y continua en `W12`; `trazaSobolevCuadrado_clasica` recupera la evaluación en las cuatro caras de las funciones clásicas $C^1$. |
| Núcleo | `trazaSobolevCuadrado_cero_de_H01` verifica $H_0^1\subseteq\ker(\mathrm{Tr})$. |
| C3.23 general | Parcial. Falta demostrar la inclusión inversa y verificar la compatibilidad con representantes continuos de elementos Sobolev arbitrarios. Las instancias de la etapa 27 siguen disponibles. |

La compilación raíz importa `TrazaSobolevCuadrado.lean`, que contiene las comprobaciones de tipos y axiomas.

## Etapa 27

La base es la [PR #28](https://github.com/MichaelMobius/tesispucp/pull/28), commit `aa07a52090171dfc4fe650362065086b1eb5fffb`. El [informe de la etapa 27](INFORME_ETAPA27.md) coteja (3.80)–(3.83).

| Resultado | Declaración y alcance |
|---|---|
| Condición de Dirichlet | `continuo_cero_frontera_mem_H01` y `frontera_puntual_igual_implica_error_H01` descargan $H_0^1$ para representantes Sobolev continuos de valores iguales en la frontera. |
| Cotas simultáneas | `cotas_simultaneas323` combina (3.81)–(3.82), con representante continuo. La versión de frontera puntual identifica el supremo de la diferencia original con la norma esencial. |
| Tasa (3.83) | `corolario323_escalar`, `corolario323_frontera_puntual` y `corolario323_poisson_levantado` derivan la tasa simultánea de P3.15 y la convergencia de ambas normas. |
| Pendiente | Núcleo del operador de traza para todo $H^1$ del cuadrado. Construcción de clases neuronales concretas y sus selecciones. |

### Reproducción actual

- Ejecutar `lake build` en la raíz del proyecto Lean con Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- Las comprobaciones de la etapa están en `TrazaCuadrado.lean` y `Corolario323.lean`.

## Historial de las etapas 20–26

### Etapa 26

La base es la [PR #27](https://github.com/MichaelMobius/tesispucp/pull/27), commit `9dd6893ec09938af52346828790e65ced3e852d8`. El [informe de la etapa 26](INFORME_ETAPA26.md) documenta la completitud y la representación espectral.

| Resultado | Declaración y alcance |
|---|---|
| Completitud | `senoDirichletLp_complete` y `modoSenoLp_complete` cubren todo $L^2$ de Lebesgue en los dos dominios. |
| Base y expansión | `baseHilbertSenoCuadrado`, `modoSenoLp_expansion` y `modoSenoLp_parseval` establecen la expansión de cualquier clase y (3.78). |
| P3.22 | `proposicion322_espectral_completa` identifica la serie con el error y demuestra (3.77) para $e\in H_0^1$ con laplaciano distribucional en $L^2$. |
| C3.23 | `poincare_cuadrado_espectral` y `poincare_cuadrado_constante_minima` verifican (3.80). `energia_cuadrado_poincare_optima` verifica (3.81) para errores dados en $H_0^1$. Quedan el puente de trazas y la tasa simultánea. |

#### Reproducción histórica de la etapa 26

- Ejecutar `lake build` en la raíz del proyecto Lean con Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- Las comprobaciones de completitud, Parseval, (3.77) y (3.80) se encuentran en `CompletitudSenoCuadrado.lean`, `Proposicion322.lean` y `PoincareEspectralCuadrado.lean`.

### Etapa 25

La base es la [PR #26](https://github.com/MichaelMobius/tesispucp/pull/26), commit `9a93fef2c757483319518c4e14f233c75b3c3baf`. El [informe de la etapa 25](INFORME_ETAPA25.md) distingue los avances espectrales de la Proposición 3.22 completa.

| Resultado | Declaración y alcance |
|---|---|
| Modos seno | Modos ortonormales para Lebesgue, de norma uno y pertenecientes a $H_0^1$ en el cuadrado, con autovalores $\pi^2(j^2+k^2)/4$. |
| Coeficientes | `coeficiente_laplaciano_modoSeno` establece (3.79) y $F_{jk}=\lambda_{jk}e_{jk}$ desde la identidad distribucional. |
| Serie y constante | `serieSeno_convergencia` prueba la convergencia absoluta y uniforme. `serieSeno_suma_L2` identifica el límite con la suma en $L^2$, con los coeficientes de $e$. `constanteEspectralCuadrado_lt` certifica $C_{\mathrm{esp}}<0.26404$. |
| Pendiente | Densidad del sistema seno en $L^2$ del intervalo y del cuadrado, Parseval, identificación de la suma con el error y estimación integrada de P3.22. C3.23, trazas generales y comparadores de Taylor/Hermite siguen pendientes. |

#### Reproducción histórica de la etapa 25

- Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- Ejecutar `lake build` en la raíz del proyecto. Los módulos nuevos `BaseSenoCuadrado`, `EspectroDirichletCuadrado`, `ConstanteEspectralCuadrado` y `Proposicion322` contienen `#check` y `#print axioms` y se construyen mediante la importación de `Proposicion322` desde `TesisPINN.lean`.

### Etapa 24

Base en la PR #25, `c0a86e6ec523dce45bee48e1f81810e408f85ed4`. El [informe de la etapa 24](INFORME_ETAPA24.md) coteja (3.76) y prepara el bloque espectral.

| Resultado | Declaración y alcance |
|---|---|
| P3.21 | `proposicion321_barrera_cuadratica` verifica la constante $1/2$. `proposicion321_Linfty_extendido` permite residuo esencial infinito y una ley de frontera de soporte completo. |
| Error de Poisson | `error_poisson321_dirichlet_exacto` y su transferencia de tasas usan una solución clásica dada. |
| Continuidad | P3.22 y C3.23 requieren base seno, integración por partes con los modos y certificación de constantes. Taylor y Hermite siguen como rutas de comparadores. |

### Etapa 23

Base en la PR #24, `976fd52bd620695cbb5dfe03a98f105b9e228779`. El [informe de la etapa 23](INFORME_ETAPA23.md) documenta la convención del operador, las normas y la separación entre existencia y estabilidad.

| Resultado | Declaración y alcance |
|---|---|
| L3.17 | `lema317_estabilidad_Linfty` verifica (3.67) en dimensión positiva arbitraria con máximo clásico de EllipticPDE y barrera exponencial. |
| T3.18 | `teorema318_dim2` verifica (3.69)–(3.70) con solución clásica dada, la frontera geométrica y la instancia de T3.8 para 2D. |
| Pendiente | Existencia clásica general de GT 6.13 y versión probabilística en dimensión general. |
| Continuidad | P3.21 reutiliza el máximo débil para la barrera cuadrática. P3.22/C3.23 requieren la ruta espectral. Taylor y Hermite suministran comparadores para las clases concretas. |

### Etapa 22

La base es la PR #23, `1da91cf7fb759e143b3549ef2e96dda4729fe2b7`. El [informe de la etapa 22](INFORME_ETAPA22.md) coteja las ecuaciones (3.44)–(3.55).

| Resultado | Declaración y alcance |
|---|---|
| Escala raíz | `radioRaizCuadrado_le_uno_iff`, `factorRaizInterior_eq`, `pesoRaizInterior_medio`. El umbral exacto de admisibilidad del radio es 324. |
| Ocupación, comparación y pérdida | `ocupacion311` demuestra la cota binomial y la cobertura eventual. `proposicion311_perdida` integra las cotas finitas y la tasa $O(m^{-\alpha/2})$ para clases con operador Hölder y comparadores aproximados. |
| Energía | `proposicion311_poisson` deduce convergencia $H^1$ y tasa $O(m^{-\alpha/4})$ para $G+\psi q$. La extensión a toda la clase con traza prescrita requiere el puente de trazas. |
| Continuidad | L3.17 y T3.18 para la estabilidad uniforme. Hermite y Taylor aportan los comparadores para C3.12 y las instancias neuronales de P3.11 y P3.15. |

### Etapa 21

Base: PR #22, `99223cb99ca288eb751832839499eaf474d83500`. El [informe de la etapa 21](INFORME_ETAPA21.md) compara la ley, la geometría, el umbral 310 y las constantes de (3.64) con sus declaraciones Lean.

| Resultado | Declaración y alcance |
|---|---|
| Ley uniforme interior y partición exacta | `medidaUniformeCuadrado`, `particiones_uniformes_cuadrado`, `masa_bola_uniforme_cuadrado`. |
| (3.64)–(3.66) | `radioLogCuadrado_admisible`, `factorLogInterior_eq`, `pesoLogInterior_eq`, `proposicion315_perdida`. Cobertura eventual y pérdida de población casi segura con comparadores y suboptimalidad de la tesis. |
| Extensión energética | `proposicion315_poisson`. Convergencia en el grafo $H^1$ y tasa $O((\log m/m)^{1/4})$ con levantamiento suave exacto y solución distribucional dada. |
| Pendiente | Extender la identificación de $H_0^1$ a toda la clase $C^{2,1/2}(\overline U)$. Instanciar la Proposición 3.11 con su radio de raíz y verificar sus pesos. |

### Etapa 20

La referencia matemática de esta etapa es el capítulo III del PDF del ZIP `Tesis_PUCP_Resumen_Conectores_20261108.zip`. La [matriz del capítulo](INVENTARIO_FORMAL_CAPITULO_III.md) registra el hash, las 27 entradas numeradas, las 94 ecuaciones, los desarrollos sin número y sus dependencias. La [auditoría de la base](AUDITORIA_MATEMATICA_PR18.md) distingue los alcances de las pruebas heredadas. Los conteos describen el material inventariado.

| Nivel | Resultados y evidencia |
|---|---|
| Verificados en el alcance de la declaración | `lema313_cobertura_logaritmica` demuestra (3.57)–(3.58) y la cobertura eventual casi segura para prefijos con $m(n)\ge n$ eventualmente. `ComparadoresAproximados` establece (3.38)–(3.41) para la instancia escalar 2D. |
| Verificados bajo hipótesis o en instancias | `proposicion314_dim2` establece (3.59)–(3.63) en 2D escalar. `proposicion310_dim2` usa (3.42) para demostrar (3.43) y las tasas uniformes para mínimos aproximados. `teorema38_dim2` da (3.26)–(3.28) para mínimos exactos. Los puentes de 3.20 dan tasas en el cuadrado con candidatos suaves `ψq` o `G+ψq`. |
| Parcialmente formalizados | Quedan las versiones en dimensión general de P3.10 y P3.14 y las instancias en clases neuronales concretas. La matriz registra las piezas disponibles de L3.3–T3.8, P3.11, P3.15, T3.18–T3.20 y L3.24–P3.27. |
| Pendientes de infraestructura o instanciación | Existencia clásica y estabilidad general, trazas Sobolev y dimensiones generales, geometría de las leyes uniformes del cuadrado, pesos y pérdidas interiores de P3.15, Poincaré óptima y base seno, clases MLP concretas, construcción de Hermite/Taylor y selección de mínimos. |

### Reproducción histórica de la etapa 20

- Base fijada en `24bdd251953f0c526a7e84aaef9dc7a28ad3e1bb`, cabeza de la [PR #21](https://github.com/MichaelMobius/tesispucp/pull/21).
- Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- Ejecutar `lake build` en `PUCP_PINN_Lean4/`. El módulo `Proposicion314` contiene las comprobaciones `#check` y `#print axioms`.
- La auditoría de hipótesis, mensurabilidad y alcance consta en el [informe de la etapa 20](INFORME_ETAPA20.md).

## Siguientes obligaciones

1. Para C3.23 en su formulación general, construir la traza de $H^1$ sobre las caras del cuadrado y demostrar que su núcleo es $H_0^1$.
2. Parametrizar ambos exponentes en la cota integral poblacional para generalizar la Proposición 3.14.
3. Separar los dos primeros puentes de aproximación. Para Taylor, demostrar extensión entera, estimación de coeficientes y cola diferenciada. Para Hermite, probar existencia y unicidad en los nodos distintos, resto uniforme e identificación boreliana de los coeficientes.
