import React from 'react'
import styled from 'styled-components'
import GenericComponent, { StyledSystemProps } from '../GenericComponent'

interface HeaderProps extends StyledSystemProps {
  clipPath?: string
}

const HeaderWrapper = styled(GenericComponent)<HeaderProps>`
  clip-path: ${(props) => props.clipPath};
  background-size: cover;
  background-position: top;
  position: relative;
  background-image: linear-gradient(
      to right bottom,
      ${(props) => props.theme.colors.primary + 'cc'},
      ${(props) => props.theme.colors.secondaryDark + 'cc'}
    ),
    url('https://picsum.photos/id/870/1000/800');
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
      backgroundImage={`url(${props.backgroundImage})`}
      clipPath={props.clipPath}
      height={props.height}
    >
      <HeaderText>{props.children}</HeaderText>
    </HeaderWrapper>
  )
}

export default Header
