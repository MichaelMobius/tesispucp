# Etapa 25 · Desarrollo espectral de Dirichlet

Base de trabajo: PR #26, commit `9a93fef2c757483319518c4e14f233c75b3c3baf`. Fuente normativa: PDF identificado por hash en el inventario del capítulo, páginas impresas 105–109 (118–122 del PDF).

## Correspondencia con el PDF

La Proposición 3.22 parte de un error $e\in H_0^1(U)$ en $U=(-1,1)^2$ con $F=-\Delta e\in L^2(U)$ en distribuciones. En Lean se usa `H1Graph.H01 volume cuadrado` y un dato `r : Lp ℝ 2 volumenPoisson` que representa $\Delta e$. Se toman los coeficientes de `-r` para representar $F$. `volumenPoisson` es el volumen de Lebesgue restringido, sin el factor $1/4$ de la ley de muestreo. Los índices naturales Lean empiezan en cero y se trasladan a las frecuencias físicas $j,k\ge1$. La ortonormalidad usa norma uno en el intervalo de longitud dos y, por producto, en el cuadrado.

| PDF | Declaración | Alcance |
|---|---|---|
| Modos de P3.22, pp. 105–106 | `senoDirichletLp_ortonormal`, `modoSenoLp_ortonormal`, `modoSenoLp_norma`, `grafoModoSeno`, `modoSeno_ecuacion` | Ortonormalidad, suavidad, frontera nula, pertenencia a $H_0^1$ y ecuación $-\Delta\phi_{jk}=\pi^2(j^2+k^2)\phi_{jk}/4$. |
| (3.79) e identidad posterior | `green_H01_bilineal`, `modoSeno_laplaciano_distribucional`, `coeficiente_laplaciano_modoSeno` | La continuidad de las dos formas lineales permite pasar de las pruebas compactas a $H_0^1$. Green en ambos órdenes da $F_{jk}=\lambda_{jk}e_{jk}$ con el signo del PDF. |
| (3.78) | `suma_coefSeno_acotada` | Bessel da la desigualdad suficiente para Cauchy–Schwarz. La igualdad de Parseval para todo $F$ sigue pendiente. |
| (3.77), constante y prueba M | `sqrt_suma_inv_autovalorSeno`, `constanteEspectralCuadrado_lt`, `serieSeno_convergencia` | Se verifica la fórmula de la constante, la cota estricta $0.26404$, la convergencia absoluta y uniforme, la continuidad, la anulación en la frontera y la estimación puntual de la serie. |
| Identificación de P3.22 | `serieSeno_suma_L2` | El límite continuo representa la suma en $L^2$ de los modos y esta suma tiene todos los coeficientes de $e$. La igualdad con $e$ requiere que los modos separen los elementos de $L^2$. |
| (3.80)–(3.83) | C3.23 | (3.80) es Poincaré óptima, (3.81) es la cota $H^1$, (3.82) es la cota $L^\infty$ y (3.83) es la tasa simultánea. Quedan pendientes. |

Las pruebas espectrales usan únicamente el grafo $H_0^1$ y el laplaciano distribucional en $L^2$, sin una premisa $H^2$. Cada modo pertenece a $H_0^1$ por la factorización suave con $(1-x^2)(1-y^2)$ y el resultado de recorte existente. Los cocientes se prolongan suavemente mediante diferencias divididas analíticas.

## Certificado numérico

Para cada denominador entero $D=(j^2+k^2)^2$, Lean verifica $D^{-1}\le (\lfloor10^{12}/D\rfloor+1)/10^{12}$. La suma de los 10 000 redondeos enteros es `424316479249`, comprobada mediante `decide +kernel`. Así $S_{100}\le 0.424316479249 < 0.424317$.

El nivel $n=\max(j,k)$ se descompone en una fila de $n$ pares y una columna de $n-1$. Cada término está acotado por $n^{-4}$. Para $n\ge2$, $(2n-1)/n^4\le (n-1)^{-2}-n^{-2}$. La suma telescópica verifica $S-S_N\le N^{-2}$ y $S<0.424417$. Se usa $\pi>3.141592$ de Mathlib y $\sqrt{0.424417}<0.65148$, demostrado al cuadrar la cota racional. La última comparación racional verifica $4\sqrt S/\pi^2<0.26404$. Este certificado es independiente del error. La cota de la cola del PDF usa una integral; la prueba Lean usa la telescópica con el mismo resultado.

## Obligación restante

Falta demostrar que el cierre del subespacio generado por `senoDirichletLp` es todo $L^2((-1,1))$ y que el cierre del generado por `modoSenoLp` es todo $L^2(U)$. La formulación equivalente para el cuadrado es que $z=0$ si todos los productos interiores de $z$ con los modos son cero. Aplicada a la diferencia entre el error y la suma en $L^2$, esta propiedad cierra la identificación casi en todas partes. Una `HilbertBasis` construida con esa densidad dará también Parseval.

Mathlib ofrece `fourierBasis` para $L^2$ complejo sobre el círculo con Haar normalizada. Su uso exige formalizar extensión impar, cambio de escala y recuperación del subespacio real, más el paso al producto. Otra ruta usa Stone–Weierstrass en el cuadrado cerrado: los cosenos de primera frecuencia separan puntos y el seno de primera frecuencia es positivo en el interior. La recurrencia del seno expresa los polinomios en los cosenos multiplicados por los senos de primera frecuencia como combinaciones de modos. Faltan formalizar la densidad y su transferencia al $L^2$ restringido.

Para C3.23, `autovalorSeno_minimo` identifica $\pi^2/2$ como el mínimo de la familia de modos. `energia_primer_modoSeno` prueba que se alcanza ese cociente de Rayleigh en un modo de norma uno. Esto descarta una constante de Poincaré menor que $\sqrt{2}/\pi$. Falta probar la admisibilidad para todo $H_0^1$. `dirichlet_poincare_sharp` de EllipticPDE da una cota por un autovalor variacional en `Sobolev.H01`, con una coercividad de partida. Identificar ese autovalor con $\pi^2/2$ y enlazar los espacios sigue siendo trabajo adicional si se toma esa ruta. La tasa (3.83) requiere además aplicar las cotas a los residuos de P3.15 con la identificación de traza pertinente. Taylor, Hermite y las clases neuronales concretas siguen en el plan general.

## Reproducción

Ejecutar `lake build` con Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. Los cuatro módulos nuevos incluyen verificaciones `#check` y `#print axioms`.

La compilación local completó 3288 trabajos. La auditoría de las declaraciones principales devuelve `propext`, `Classical.choice` y `Quot.sound`. El certificado entero privado depende únicamente de `propext`.
