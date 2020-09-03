import { Theme } from 'styled-system'

export interface Space {
  NONE: number
  XS: number
  S: number
  M: number
  L: number
  XL: number
  XXL: number
}

export interface ThemeColors {
  primary: string
  primaryLight: string
  primaryDark: string
  secondaryLight: string
  secondaryDark: string
  tertiaryLight: string
  tertiaryDark: string
  greyLight1: string
  greyLight2: string
  greyDark: string
  greyDark2: string
  greyDark3: string
  white: string
  black: string
  link: string
  success: string
  warning: string
  error: string
  heading: string
  text: string
  disabled: string
  border: string
}

export const space: Space = {
  NONE: 0,
  XS: 2,
  S: 4,
  M: 8,
  L: 16,
  XL: 32,
  XXL: 64,
}

export const breakpoints: any = ['319px', '424px', '767px', '1023px', '1200']

breakpoints.sm = breakpoints[0]
breakpoints.md = breakpoints[1]
breakpoints.lg = breakpoints[2]
breakpoints.xl = breakpoints[3]
breakpoints.xxl = breakpoints[4]

// export const fontSizes: number[] = [
//   12,
//   14,
//   15,
//   16,
//   17,
//   18,
//   19,
//   20,
//   21,
//   22,
//   24,
//   27,
//   28,
//   30,
//   32,
//   37,
//   39,
//   41,
//   43,
//   50,
//   51,
//   52,
//   57,
// ]

export const colors: ThemeColors = {
  primary: '#55c57a',
  primaryLight: '#7ed56f',
  primaryDark: '#28b485',
  secondaryLight: '#ffb900',
  secondaryDark: '#ff7730',
  tertiaryLight: '#2998ff',
  tertiaryDark: '#5643fa',
  greyLight1: '#f7f7f7',
  greyLight2: '#eee',
  greyDark: '#777',
  greyDark2: '#999',
  greyDark3: '#333',
  white: '#fff',
  black: '#000',
  link: '#1890ff',
  success: '#52c41a',
  warning: '#faad14',
  error: '#e84118',
  heading: '#423EA2',
  text: '#000',
  disabled: '#f5222d',
  border: '#423EA2',
}

export const defaultTheme: Theme = {
  space: {
    ...space,
  },
  // fontSizes,
  breakpoints,
  colors: {
    ...colors,
  },
}
