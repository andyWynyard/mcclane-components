import React from 'react'
import styled from 'styled-components'
import GenericComponent, { StyledSystemProps } from '../GenericComponent'

interface HeaderProps extends StyledSystemProps {
  clipPath: string
}

const HeaderWrapper = styled(GenericComponent)<HeaderProps>`
  clip-path: ${(props) => props.clipPath};
  background-size: cover;
  background-position: top;
  position: relative;
  background-image: ${(props) => props.backgroundImage};
`

const HeaderText = styled.div`
  position: absolute;
  top: 40%;
  left: 50%;
  transform: translate(-50%, -50%);
  text-align: center;
`

const Header: React.FC<HeaderProps> = (props) => {
  return (
    <HeaderWrapper
      backgroundImage={props.backgroundImage}
      clipPath={props.clipPath}
      height={props.height}
    >
      <HeaderText>{props.children}</HeaderText>
    </HeaderWrapper>
  )
}

export default Header
