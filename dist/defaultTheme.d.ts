import * as CSS from 'csstype';
import { Theme } from 'styled-system';
export interface Space {
    NONE: number;
    XS: number;
    S: number;
    M: number;
    L: number;
    XL: number;
    XXL: number;
}
export interface ThemeColors {
    primary: CSS.ColorProperty;
    primaryLight: CSS.ColorProperty;
    primaryDark: CSS.ColorProperty;
    secondaryLight: CSS.ColorProperty;
    secondaryDark: CSS.ColorProperty;
    tertiaryLight: CSS.ColorProperty;
    tertiaryDark: CSS.ColorProperty;
    greyLight1: CSS.ColorProperty;
    greyLight2: CSS.ColorProperty;
    greyDark: CSS.ColorProperty;
    greyDark2: CSS.ColorProperty;
    greyDark3: CSS.ColorProperty;
    white: CSS.ColorProperty;
    black: CSS.ColorProperty;
    link: CSS.ColorProperty;
    success: CSS.ColorProperty;
    warning: CSS.ColorProperty;
    error: CSS.ColorProperty;
    heading: CSS.ColorProperty;
    text: CSS.ColorProperty;
    disabled: CSS.ColorProperty;
    border: CSS.ColorProperty;
}
export declare const space: Space;
export declare const breakpoints: any;
export declare const fontSizes: number[];
export declare const colors: ThemeColors;
export declare const defaultTheme: Theme;
