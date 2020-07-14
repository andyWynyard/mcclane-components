import React from 'react'
import styled from 'styled-components'
import {
  color,
  space,
  SpaceProps,
  typography,
  TypographyProps,
  layout,
  LayoutProps,
  flexbox,
  FlexboxProps,
  grid,
  GridProps,
  background,
  BackgroundProps,
  border,
  BorderProps,
  position,
  PositionProps,
  shadow,
  ShadowProps,
} from 'styled-system'

export type StyledSystemProps = SpaceProps &
  TypographyProps &
  LayoutProps &
  FlexboxProps &
  GridProps &
  BackgroundProps &
  BorderProps &
  PositionProps &
  ShadowProps & {
    color?: string
    as?: keyof JSX.IntrinsicElements | React.ComponentType<any>
  }

export default styled.div`
  ${space}
  ${color}
  ${typography}
  ${layout}
  ${flexbox}
  ${grid}
  ${background}
  ${border}
  ${position} 
  ${shadow}
`
