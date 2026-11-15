# Estado verificable de la formalización del capítulo III

## Estado actual · etapa 39

Base [PR #40](https://github.com/MichaelMobius/tesispucp/pull/40), commit `f32acd06d334b1c7618dd035a7d813f61e88cbc1`.

| Resultado | Declaración y alcance |
|---|---|
| L3.19 en dimensión positiva | `laplaciano_dimensional_implica_prueba`, `green_dimensional` y `lema319_dimensional` demuestran (3.71) sobre abiertos acotados. `lema319_constante_dada` conserva cualquier constante admisible. |
| T3.20 determinista | `estimacion320_dimensional` verifica (3.74) para pares Sobolev con error en $H_0^1$. `estimacion320_de_trazas_iguales` usa una traza abstracta con núcleo caracterizado. |
| T3.20 probabilístico | `teorema320_dimension_ge_dos` deriva (3.72), (3.73) y (3.75) para los mismos mínimos y prefijos de T3.8. `teorema320_unidimensional` usa el modelo con extremos deterministas. Ambas ramas reciben la condición afín en $H_0^1$. |
| T3.18 | `teorema318_dimension_ge_dos` conecta T3.8 y L3.17 con una solución clásica dada para obtener (3.69)–(3.70). |

El [informe de la etapa 39](INFORME_ETAPA39.md) distingue las premisas de traza, las identificaciones de los representantes y la existencia clásica pendiente.

## Etapa 38

Base [PR #39](https://github.com/MichaelMobius/tesispucp/pull/39), commit `4a9f8a6f15003f0aa425bbe350c0a64de540f5e9`.

| Resultado | Declaración y alcance |
|---|---|
| T3.4 en d=1 | `teorema34_unidimensional` verifica (3.12) en un evento medible común a todos los candidatos, con un prefijo i.i.d. interior, ambos extremos deterministas y regularización exclusivamente interior. |
| T3.8 en d=1 | `teorema38_unidimensional_evento` y `teorema38_unidimensional` prueban la cota finita, la tasa poblacional y la convergencia uniforme casi segura de ambos residuos. Las tasas uniformes salen de L3.9 y del control directo de ambos extremos. |
| P3.10 dimensional | `cotas310_dimensional_bajo_cobertura` obtiene (3.39)–(3.41). `proposicion310_dimensional` usa (3.42) para probar (3.43) y las tasas uniformes con dos exponentes de masa positivos. Recupera d=2 y la fórmula geométrica para todo d≥2. |
| C3.12 dimensional | `corolario312_premisas310_dimensional` transfiere la aproximación fuerte y la brecha de optimización a las premisas de P3.10 para los mismos prefijos. |

El [informe de la etapa 38](INFORME_ETAPA38.md) coteja las hipótesis normativas y las declaraciones verificadas.

## Etapa 37

Base [PR #38](https://github.com/MichaelMobius/tesispucp/pull/38), commit `4581fd0b2d07b6b6dd36723c3178a69b58660ebb`.

| Resultado | Declaración y alcance |
|---|---|
| T3.4 en d≥2 | `teorema34_dimensional` demuestra (3.10)–(3.11) para todos los candidatos escalares en un mismo evento medible. |
| T3.8 en d≥2 | `teorema38_evento_dimensional` da (3.26) en muestra finita. `teorema38_dimension_ge_dos` obtiene (3.26)–(3.28) casi seguramente a partir de las premisas muestrales y variacionales. |
| P3.14 | `proposicion314_evento_dimensional` y `proposicion314_dimensional` verifican la alternativa logarítmica para los dos exponentes de masa. |
| Cuadrado | Ambos teoremas recuperan los enunciados 2D. `teorema34_cuadrado_dos_familias` instancia los prefijos del producto de las leyes uniformes de área y longitud. |

El [informe de la etapa 37](INFORME_ETAPA37.md) registra las constantes, los cuantificadores y la rama unidimensional pendiente.

## Etapa 36

Base [PR #37](https://github.com/MichaelMobius/tesispucp/pull/37), commit `d6d84bfe06d8bf55109af3b5a86452d3168bc8f9`.

| Resultado | Declaración y alcance |
|---|---|
| L3.9 global, (3.34) | `lema39_global_acotado` incluye el caso de energía nula y ambos regímenes de radio, con constante geométrica independiente de la función. `lema39_tasa` recupera los exponentes de (3.28). |
| H3.2 en el cuadrado | `datosMasa38_frontera_cuadrado` usa la longitud Hausdorff normalizada y las constantes impresas $c_b=1/12$ y $C_b=1$. Los dos registros `Muestreo38` viven en un espacio común con sucesiones completas independientes. |
| Cobertura dimensional | `masa_bola_inferior_dimensional`, `lema36_cobertura_dimensional` y `perdidaPoblacional_le_sumas_dimensional` parametrizan diámetro y exponentes de masa. La integración de T3.4 y T3.8 sigue en 2D. |

El [informe de la etapa 36](INFORME_ETAPA36.md) registra las constantes, los resultados de biblioteca y el alcance que queda pendiente.

## Etapa 35

Base [PR #36](https://github.com/MichaelMobius/tesispucp/pull/36), commit `1b3fe97bbbba79ebb599a6e96280c92e7b365179`.

| Resultado | Declaración y alcance |
|---|---|
| Régimen raíz (3.94) | `convergencia_neuronal_manufacturada_raiz` prueba selección boreliana, mínimo global, Dirichlet exacto y las tasas casi seguras $m^{-1/4}$ de pérdida y $m^{-1/8}$ de error conjunto $H^1+L^\infty$. El selector minimiza la norma euclídea de coeficientes entre mínimos. |
| C3.12 | `corolario312` deduce (3.36)–(3.37) de la aproximación fuerte con operadores lineales continuos entre espacios normados y evaluaciones Hölder. `corolario312_premisas310` entrega las premisas variacionales de P3.10 para la instancia escalar 2D. Taylor cumple las tolerancias para los dos pesos. |
| Auditoría | El inventario de los 27 rótulos separa los resultados del cuadrado de las extensiones del capítulo. Los regímenes manufacturados están demostrados con los respectivos funcionales. |

Los detalles de las hipótesis y la correspondencia están en el [informe de la etapa 35](INFORME_ETAPA35.md).

## Etapa 34

La base es la [PR #35](https://github.com/MichaelMobius/tesispucp/pull/35), commit `5fc6be834faffad9121aade7bdd52ce994801514`.

| Resultado | Declaración y alcance |
|---|---|
| Minimización neuronal manufacturada | `convergencia_neuronal_manufacturada` verifica la tasa casi segura logarítmica en $H^1+L^\infty$ para el selector de C3.26. |
| Taylor | `resto_taylorManufacturada_c3` y `proposicion327` verifican (3.92), (3.93), admisibilidad y los dos criterios de tolerancia. |
| Hermite | `factorHermite325_resto_c3_base_dos_tercios` verifica (3.90) y `comparador325_horner` certifica ancho ocho y profundidad $8\max(r_x,r_y)+4$. |

El [informe de la etapa 34](INFORME_ETAPA34.md) documenta la normalización de la pérdida, la constante espectral y el alcance de las tasas.


## Etapa 33

La base es la [PR #34](https://github.com/MichaelMobius/tesispucp/pull/34), commit `715345fb5ccea89aa8f7d5b22a699db631b0b1f6`.

| Resultado | Declaración y alcance |
|---|---|
| Redes de arquitectura fija | `lema31_regularidad`, `lema31_cotas_direccionales` y `lema31_precompacidad` en la formulación de Fréchet. |
| Ocupación y generalización | `lema36_fallo_parametro` y `lema36_shin` recuperan las cotas de ocupación. `teorema34_dim2_explicito` da un evento medible simultáneo para el caso escalar 2D. |
| Dos escalas del Teorema 3.8 | `teorema38_apartado1_dim2` da la cota de muestra finita. `teorema38_dim2` da las conclusiones casi seguras de la familia. |
| Convergencia de la clase manufacturada | `perdida_minimizadores326_logaritmica` aplica P3.15 a los mínimos borelianos con el peso logarítmico. |
| Corolario 3.26 | `corolario326` selecciona pesos borelianos para un mínimo global del funcional original y demuestra las cotas de (3.91). |

El [informe de la etapa 33](INFORME_ETAPA33.md) registra las diferencias respecto de los enunciados de Shin y la tesis, y el estado de (3.90) y de la red de ancho ocho.


## Etapa 32

La base es la [PR #33](https://github.com/MichaelMobius/tesispucp/pull/33), commit `14451ed0184e91ad51cb42d56bd498bcd7a00c55`.

| Resultado | Declaración y alcance |
|---|---|
| Resto de Hermite | `restoContornoHermite_polinomio_cero` y `factorHermite325_formula` demuestran (3.89) con numerador $a$. |
| Regularidad | `factorHermite325_derivadas_resto_uniforme`, `comparador325_c3_uniforme` y `laplaciano_comparador325_holder_uniforme` verifican cotas uniformes en la clausura. La tasa del resto usa $(5/6)^N$. |
| Mensurabilidad e integración | `coeficientesHermite325_borel` y `proposicion325_arquitectura_comun` verifican la selección y la realizan en la arquitectura común de L3.24. |
| Pendientes | Quedan la red particular de ancho ocho y la tasa específica de (3.90) con base $2/3$. C3.26 requiere existencia y selección boreliana de minimizadores. |

El [informe de la etapa 32](INFORME_ETAPA32.md) registra las constantes, la matriz de Vandermonde confluente y la correspondencia exacta con la tesis.


## Etapa 31

La base es la [PR #32](https://github.com/MichaelMobius/tesispucp/pull/32), commit `4165c9c4cc2b43fdf53ba6910cf5f119f0e11f47`.

| Resultado | Declaración y alcance |
|---|---|
| Hermite univariado y tensorial | `existe_unico_hermite`, `hermiteMuestra_jet` y `hermite325_jet_mixto` verifican los jets, incluso si la muestra contiene coordenadas repetidas. |
| Interpolación exacta | `proposicion325_interpolacion_exacta` verifica Dirichlet, realización en la red común, residuo nodal y pérdida empírica cero. |
| Cota y selección | La prolongación entera, los lemas de contorno y los estratos borelianos están construidos. Quedan (3.89) con numerador $a$, la cota uniforme y la selección global de coeficientes. |

El [informe de la etapa 31](INFORME_ETAPA31.md) delimita las conclusiones de P3.25 y las obligaciones para C3.26.

## Etapa 30

La base es la [PR #31](https://github.com/MichaelMobius/tesispucp/pull/31), commit `aeb8621ab5b9c8e398aaf7607b72961cfdd59a9d`.

| Resultado | Declaración y alcance |
|---|---|
| L3.24 | `lema324` realiza exactamente la clase polinómica mediante capas cuadráticas fijas y salida lineal variable, con las cotas de la tesis. |
| Coordenadas polinómicas | `clase324_eq_polinomios` identifica el grado parcial. `mapaCoeficientes324_inyectivo` identifica unívocamente los coeficientes. |
| Próxima obligación | P3.25 requiere construir comparadores de Hermite, verificar su cota uniforme y probar la selección boreliana. |

El [informe de la etapa 30](INFORME_ETAPA30.md) describe la evaluación y los recuentos.

## Etapa 29

La base es la [PR #30](https://github.com/MichaelMobius/tesispucp/pull/30), commit `74f2140f7762a2c851aa2038629a37f7dccf9454`. El [informe de la etapa 29](INFORME_ETAPA29.md) documenta el núcleo de la traza y su aplicación.

| Resultado | Declaración y alcance |
|---|---|
| Fórmula de frontera | `integral_partes_traza_cuadrado` da los términos de cara para toda función del espacio Sobolev. |
| Núcleo | `extension_cero_traza_nula` conserva la derivada débil. `nucleo_trazaSobolevCuadrado_eq_H01` prueba la caracterización mediante contracción, convergencia $L^2$ y molificación. |
| Representantes continuos | `trazaSobolevCuadrado_continua` recupera su restricción en las cuatro caras. |
| C3.23 | `cotas_simultaneas323_traza` verifica las cotas para dos elementos de $H^1$ de igual traza. `corolario323_traza` integra la tasa y convergencia de ambas normas para las selecciones escalares de P3.15. |

## Etapa 28

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
| Parcialmente formalizados | Quedan extensiones de L3.1, T3.18–T3.20 y las instancias para otras clases neuronales o geometrías. La matriz distingue estas obligaciones de las pruebas de la clase manufacturada. |
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
